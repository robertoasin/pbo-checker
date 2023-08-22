/***********************************************************************
Copyright (c) 2014-2020, Jan Elffers
Copyright (c) 2019-2021, Jo Devriendt
Copyright (c) 2020-2021, Stephan Gocht
Copyright (c) 2014-2021, Jakob Nordström

Parts of the code were copied or adapted from MiniSat.

MiniSat -- Copyright (c) 2003-2006, Niklas Een, Niklas Sorensson
           Copyright (c) 2007-2010  Niklas Sorensson

Permission is hereby granted, free of charge, to any person obtaining a
copy of this software and associated documentation files (the
"Software"), to deal in the Software without restriction, including
without limitation the rights to use, copy, modify, merge, publish,
distribute, sublicense, and/or sell copies of the Software, and to
permit persons to whom the Software is furnished to do so, subject to
the following conditions:

The above copyright notice and this permission notice shall be included
in all copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS
OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF
MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND
NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE
LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION
OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN CONNECTION
WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
***********************************************************************/

#include "run.hpp"
#include "ConstrExp.hpp"
#include "Solver.hpp"

namespace rs {

Solver run::solver;

run::LazyVar::LazyVar(Solver& slvr, const Ce32 cardCore, int cardUpperBound, Var startVar)
    : solver(slvr), coveredVars(cardCore->getDegree()), upperBound(cardUpperBound) {
  assert(cardCore->isCardinality());
  cardCore->toSimple()->copyTo(atLeast);
  atLeast.toNormalFormLit();
  assert(atLeast.rhs == cardCore->getDegree());
  atMost.rhs = -atLeast.rhs;
  atMost.terms.reserve(atLeast.terms.size());
  for (auto& t : atLeast.terms) {
    atMost.terms.emplace_back(-t.c, t.l);
  }
  currentVar = startVar;
  atLeast.terms.emplace_back(-1, startVar);
  atMost.terms.emplace_back(remainingVars(), startVar);
  ++coveredVars;
}

run::LazyVar::~LazyVar() {
  solver.dropExternal(atLeastID, false, false);
  solver.dropExternal(atMostID, false, false);
}

int run::LazyVar::remainingVars() const { return upperBound - coveredVars; }

void run::LazyVar::setUpperBound(int cardUpperBound) {
  assert(upperBound >= cardUpperBound);
  upperBound = cardUpperBound;
}

void run::LazyVar::addVar(Var v, bool reified) {
  currentVar = v;
  if (reified) {
    Term<int>& last = atLeast.terms.back();
    last = {last.c - 1, v};
    --atMost.rhs;
    Term<int>& last2 = atMost.terms.back();
    last2 = {remainingVars(), v};
  } else {
    atLeast.terms.emplace_back(-1, v);
    Term<int>& last = atMost.terms.back();
    last = {1, last.l};
    atMost.terms.emplace_back(remainingVars(), v);
  }
  ++coveredVars;
}

ID run::LazyVar::addAtLeastConstraint(bool reified) {
  assert(atLeast.terms.back().l == currentVar);
  solver.dropExternal(atLeastID, !reified, false);
  atLeastID = solver.addConstraint(atLeast, Origin::COREGUIDED).second;
  return atLeastID;
}

ID run::LazyVar::addAtMostConstraint(bool reified) {
  assert(atMost.terms.back().l == currentVar);
  solver.dropExternal(atMostID, !reified, false);
  atMostID = solver.addConstraint(atMost, Origin::COREGUIDED).second;
  return atMostID;
}

ID run::LazyVar::addSymBreakingConstraint(Var prevvar) const {
  assert(prevvar < currentVar);
  // y-- + ~y >= 1 (equivalent to y-- >= y)
  return solver.addConstraint(ConstrSimple32({{1, prevvar}, {1, -currentVar}}, 1), Origin::COREGUIDED).second;
}

ID run::LazyVar::addFinalAtMost(bool reified) {
  solver.dropExternal(atMostID, !reified, false);
  Term<int>& last = atMost.terms.back();
  last = {1, last.l};
  atMostID = solver.addConstraint(atMost, Origin::COREGUIDED).second;
  return atMostID;
}

std::ostream& run::operator<<(std::ostream& o, const std::shared_ptr<LazyVar> lv) {
  o << lv->atLeast << "\n" << lv->atMost;
  return o;
}

void run::decide() {
  while (true) {
    SolveState reply = aux::timeCall<SolveState>([&] { return solver.solve().state; }, stats.SOLVETIME);
    assert(reply != SolveState::INCONSISTENT);
    if (reply == SolveState::SAT)
      quit::exit_SAT(solver);
    else if (reply == SolveState::UNSAT)
      quit::exit_UNSAT(solver);
  }
}

void run::run(CeArb objective, std::string solFileName) {
  stats.RUNSTARTTIME = aux::cpuTime();
  //std::cout << "c #variables " << solver.getNbOrigVars() << " #constraints " << solver.getNbConstraints()<< std::endl;
  try {
    if (objective->vars.size() > 0) {
      objective->stopLogging();
      objective->removeUnitsAndZeroes(solver.getLevel(), solver.getPos(), false);
      BigVal maxVal = objective->getCutoffVal();
      if (maxVal <= limit32) {  // TODO: try to internalize this check in ConstrExp
        Ce32 result = solver.cePools.take32();
        objective->copyTo(result);
        Optimization optim(result);
	optim.check_solution(solFileName);
      } else if (maxVal <= limit64) {
        Ce64 result = solver.cePools.take64();
        objective->copyTo(result);
        Optimization optim(result);
	optim.check_solution(solFileName);
      } else if (maxVal <= BigVal(limit96)) {
        Ce96 result = solver.cePools.take96();
        objective->copyTo(result);
        Optimization optim(result);
	optim.check_solution(solFileName);
      } else if (maxVal <= BigVal(limit128)) {
        Ce128 result = solver.cePools.take128();
        objective->copyTo(result);
        Optimization optim(result);
	optim.check_solution(solFileName);
      } else {
        CeArb result = solver.cePools.takeArb();
        objective->copyTo(result);
        Optimization<bigint, bigint> optim(result);
        optim.check_solution(solFileName);
      }
    }else{
      Ce32 result = solver.cePools.take32();
      objective->copyTo(result);
      Optimization optim(result);
      optim.check_solution(solFileName);
    }
  } catch (const AsynchronousInterrupt& ai) {
    std::cout << "c " << ai.what() << std::endl;
    quit::exit_INDETERMINATE(solver);
  }
}

}  // namespace rs

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

#include <csignal>
#include <fstream>
#include <memory>
#include "auxiliary.hpp"
#include "globals.hpp"
#include "parsing.hpp"
#include "run.hpp"

namespace rs {

bool asynch_interrupt;
Options options;
Stats stats;

}  // namespace rs

static void SIGINT_interrupt([[maybe_unused]] int signum) { rs::asynch_interrupt = true; }

static void SIGINT_exit([[maybe_unused]] int signum) {
  printf("\n*** INTERRUPTED ***\n");
  exit(1);
}

int main(int argc, char** argv) {
  rs::stats.STARTTIME = rs::aux::cpuTime();
  rs::asynch_interrupt = false;

  signal(SIGINT, SIGINT_exit);
  signal(SIGTERM, SIGINT_exit);
  signal(SIGXCPU, SIGINT_exit);

  std::string formulaName(argv[1]);
  std::string solName(argv[2]);
  
  rs::run::solver.init();
  rs::CeArb objective = rs::run::solver.cePools.takeArb();

  std::ifstream fin(formulaName);
  if (!fin) rs::quit::exit_ERROR({"Could not open ", formulaName});
  rs::parsing::file_read(fin, rs::run::solver, objective);

  signal(SIGINT, SIGINT_interrupt);
  signal(SIGTERM, SIGINT_interrupt);
  signal(SIGXCPU, SIGINT_interrupt);

  //rs::run::solver.initLP(objective);

  rs::run::run(objective,solName);
}

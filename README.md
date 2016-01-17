# ICE -- Integration-By-Parts Chooser of Equations

ICE is a program to choose a maximal linearly independent subset from
a given set of Integration-by-Parts and/or Lorentz Invariance
equations.

## Installation

The easiest way to compile the program from source is to use the stack
build tool, avaialble at https://github.com/commercialhaskell/stack.
Executing
```
stack install
```
in the directory containing the sources of ice will install the ice
executable to =$HOME/.local/bin/ice=.  You can either add that
directory to your =PATH=, or use stack to run ice, as in
```
stack exec -- ice -id -im example/se1l.in
```
The stack tool will automatically download the GHC compiler and all
dependencies.

## Documentation

A Manual is found in ./doc/ice-manual.pdf, and an example input file
can be found in example/se1l.in.

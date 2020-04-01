# Sat Solver

This is a repository containing SAT solver written in python. 

## How to use it
To use it first clone repository with `git clone https://github.com/gasperxy/SatSolver.git`.

Then open cmd or terminal and write `python satsolver.py "input_filename.txt" "output_filename.txt"`

# Implementation Notes

Sat solver uses dpll algorithem to solve satisfiability of a CNF formula. On first implementation solver worked but there were not any optimizations for speed.
First thing we focused on was unit propagation since from online sources we know that sat solver spend most time doing unit propagation.

After few iteration unit propagation (and propagation itself) looks like it worked a bit faster. There was improvment especially in harder cases of cnf formula.

## Split variable heuristics

At initialization of a cnf formula we stored each variable and their occurrances in both positive and negative parity. This enables us to calculate many heuristics
based on distribution of variables inside a formula. We have tried some different heuristics and it looks like DLS (dynamic largest sum) performed best results on our tests.
Dynamic largest sum heristics chooses a variable that has most occurrences in formula and chooses value that a variable occurres with the most in a formula. This
aims to reduce as many clauses as possible. Using heuristic turns out to be a major improvment in test runs.

## Tests

For testing porpuses we used benchmarking site https://www.cs.ubc.ca/~hoos/SATLIB/benchm.html where we try many satisfiable and unsatisfiable formulas.

Some of the probles we solved during testing :
 * Graph-3 and Graph-5 coloring
 * 3-Sat 
 * Sudoku (from e-classroom)
 * Some unsatisfiable formulas 


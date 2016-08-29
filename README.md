# GenPSAT
GenPSAT solver
* decides the satisfiability of linear inequalities involving probabilities of classical propositional formulas

## Requires
* java
* gurobi solver (tested with v6.5)

## Build
Use `javac -d bin src/genpsatmip.java` to build

## Run
Use `java -cp bin/ genpsatmip filename` to run the program on file filename.

## Input file format
The solver accepts input files in the following format:
* lines that begin with a `c` are comment lines
* one line that states size of problem such as `p cnf nvar nclauses nprobs`, where 
 * `nvar` is the number of propositional variables
 * `nclauses` is the number of propositional clauses
 * `nprobs` is the number of probabilistic clauses
* followed by `nclauses` propositional clauses which are a sequence of 3 non-null numbers (3CNF) between -nvar and nvar ending with 0 on the same line. Negative numbers correspond to negated variables.
* followed by `nprobs` probabilistic clauses which are of the form TYPE (q<sub>0</sub>)v<sub>0</sub> ... (q<sub>n</sub>)v<sub>n</sub> i where TYPE can be EQ, SG, SL, GE, LE, DI (standing for equal, strictly greater/less, greater/less or equal and different), q<sub>i</sub> and i are rational numbers and v<sub>i</sub> are variable names.

One example of this format is the following

```
c usage p cnf nvar nclauses nprobs
p cnf 3 2 1
1 -2 3 0
2 1 -3 0
EQ (-0.3)1 (3)2 3
```

which corresponds to the GenPSAT problem 
![genpsat](https://github.com/fcasal/genpsat/blob/master/img/ex1.jpg?raw=true)

## Releases
* v0.1 -- Initial release in August 2016

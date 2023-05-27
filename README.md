CoqQFFP : Towards A Certified SMT QF_FP Solver
=======
CoqQFFP is an SMT QF_FP solver based on the certified SMT QF_BV solver [CoqQFBV](https://github.com/fmlab-iis/coq-qfbv). It accepts SMT QF_FP queries in the
[SMTLIB2](http://smtlib.cs.uiowa.edu) format. CoqQFFP supports all operations specified in the [SMT Floating-point Theory](http://smtlib.cs.uiowa.edu/theories-FloatingPoint.shtml), except for conversions to other sorts.

Given an SMTLIB2 file, CoqQFFP
first converts the assertions in the file into a formal QF_FP expression.
A QF_BV expression in the formal syntax of CoqQFBV is then constructed from the QF_FP expression by a word-blasting procedure with a trust base in Coq. The certified QF_BV solving procedure from CoqQFBV is invoked to solve the QF_BV expression, and details can be found on [CoqQFBV](https://github.com/fmlab-iis/coq-qfbv). 

The source code of CoqQFFP has been derived and modified from CoqQFBV. This includes the addition of a word-blasting algorithm, formalization of the SMTLIB floating-point theory, and modifications to the OCaml front-end of CoqQFBV. The new Coq code about floating-point encoding is included in src/fq2bvq. With the code extraction mechanism of Coq, the certified OCaml code is extracted in src/ocaml/extraction and is used by the SMT QF_FP solver in src/ocaml.

A video demonstration is available at https://youtu.be/BVpi3FyATCQ.
Installation
============

To compile the formalization of the word-blasting procedure and the certified bit-blasting procedure in
CoqQFFP, the following packages are required.

* [Coq](https://coq.inria.fr) 8.15.0
* [MathComp](https://github.com/math-comp/math-comp) 1.14.0

To compile the SMT QF_FP solver of CoqQFBV, the following packages
are required.

* [OCaml](https://ocaml.org) 4.13.1
* [Dune](https://dune.build) 2.9.1 (or newer versions)
* [Zarith](https://github.com/ocaml/Zarith) 1.12.1 (or newer versions)

To run CoqQFFP, the following tools are required.

* [kissat](http://fmv.jku.at/kissat/)
* [gratgen](https://www21.in.tum.de/~lammich/grat/) and
  [gratchk](https://www21.in.tum.de/~lammich/grat/)

Make sure that the tools are installed and can be found in the PATH
environment variable.


On Ubuntu
---------

On Ubuntu 22.04 LTS, the packages for compilation can be installed by the
following command.

    $ sudo apt install ocaml ocaml-dune libzarith-ocaml-dev coq libssreflect-coq

The script setup-ubuntu can be used to install all required packages
and external tools on Ubuntu 22.04.

Compilation
-----------

Run the following commands in the root directory of the CoqQFFP project to
compile the Coq formalization of the word-blasting procedure and certified bit-blasting procedure.

    $ make -C lib/coq-nbits
    $ make -C lib/coq-ssrlib
    $ make

Run the following command in the directory src/ocaml to compile the
SMT QF_FP solver of CoqQFFP.

    $ dune build

The binary of CoqQFFP can be found in src/ocaml/_build/default.


Usage
=====

Assume the current directory is src/ocaml. To check the satisfiability of
a QF_FP query in an SMTLIB2 file query.smt2, run the following command.

    $ _build/default/coqQFFP.exe query.smt2

To see some statistics, run the following command.

    $ _build/default/coqQFFP.exe -verbose query.smt2

If the result is sat with assignments, CoqQFFP verifies whether the SMT assignments satisfy the QF_FP expression using a certified procedure, and reports'sat'. Using option '-no-certify-sat' to disable the check.

    $ _build/default/coqQFFP.exe -no-certify-sat query.smt2

If the result is unsat with a certificate, CoqQFFP verifies the certificate using the certified SAT solver certificate checking tool chain [GRAT](https://www21.in.tum.de/~lammich/grat/). Using option '-no-certify-unsat' to disable the verification.

    $ _build/default/coqQFFP.exe -no-certify-unsat query.smt2

To see more available arguments, run the following command.

    $ _build/default/coqQFFP.exe -help


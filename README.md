intuitR
=======

An efficient SAT-based theorem prover for Intuitionistic Propostional Logic [1].

It is implemented on the top of the prover [intuit](https://github.com/koengit/intuit)
by Claessen and Rosen.


In the directory `documents` you can find:

-  a full version of the paper (with appendix);
-  the slides used at the CADE 2021 conference.



The directory `examples` contains the output files generated by
`intuitR` with the formulas &chi; and &psi; defined in Examples 1 and 2 [1].


An implementation of `intuit` with the trace of computations and the
construction of derivations/countermodels is available at the
directory `intuitT` (see the corresponding README file).


References
----------


[1] Fiorentini Camillo.  Efficient SAT-based Proof Search in Intuitionistic Propositional Logic.
In: Platzer A., Sutcliffe G. (eds) Automated Deduction – CADE 28. CADE 2021. LNCS, vol 12699. Springer, Cham (2021).

[https://doi.org/10.1007/978-3-030-79876-5_13](https://doi.org/10.1007/978-3-030-79876-5_13) (Open Access)





Installation
------------

You have to install:

- the [Haskell Platform](https://www.haskell.org/platform/)
- the [Haskell Cabal](https://www.haskell.org/cabal/)


From the  root directory (i.e., the directory containing the file  `intuitR.cabal`) run the command:

```console
 cabal install
```

It should be printed a message like this:

```console
 ....
 Symlinking 'intuitR' to ...
```


meanining that `intuitR` is the command to launch the prover.
The executable `intuitR` is located inside the directory `dist-newstyle`.


Running
-------

The input formula must be written in a text file using the
[TPTP syntax](http://tptp.cs.miami.edu/TPTP/QuickGuide/Problems.html) (see next section);
the files `chi.p` and `psi.p` in  the directory `test` encodes
the formulas  &chi; and &psi; (see Examples 1 and 2).




To decide the validity of the formula in the file `form.p`, run the command:

```console
 intuitR form.p
```

To generate the output files with the trace of the computation and the derivation or countermodel:

```console
 intuitR -t form.p
```

A directory out-...  will be created containing  the source files (.tex and .gv).
To compile them, move into such a directory and enter the command `make`.

Note that:

-  files .tex  are compiled using  `pdflatex`; derivations are built using the Latex package [proof](http://research.nii.ac.jp/~tatsuta/proof-sty.html).

-  files .gv   are compiled using the command `dot` of
   [Graphviz - Graph Visualization Software](https://graphviz.org/).

Both the commands `pdflatex` and `dot` must be in your PATH variable.
If something goes wrong, try to execute the commands:

```console
pdflatex your_file.tex
dot your_file.gv -Tpng -o out.png
```


We have implemented four different  trace levels:

```console
 intuitR -t0 form.p     // minimum trace level, no output files 
 intuitR -t1 form.p     // medium  trace level, no output files 
 intuitR -t2 form.p     // maximum trace level, no output files 
 intuitR -t  form.p     // maximum trace level  with output files 
```



TPTP Syntax
-----------

The TPTP syntax is extensively described [here](http://tptp.cs.miami.edu/TPTP/QuickGuide/Problems.html),
see also the files .p in the directories `Benchmarks` and `test`.

For small formulas F, you can write in the input file the line

```console
  fof(label, conjecture, F).
```

where:

```console
  F :=     atom          // prop. variable
        |  $false        // false
        |   ~F           // not 
        |  F & F         // and
        |  F | F         // or
        |  F => F        // implication 
        |  F <=> F       // bi-implication
```

Examples of definitions (to be written in distinct files): 

```console
 fof(example1, conjecture, ((p1 | p2) & (p1 => q) & (p2 <=> q))   => $false | q ).
 fof(example2, conjecture,  (a => b) | (b => a) ).
 fof(example3, conjecture,  ~~((a => b) | (b => a)) ). 
```

Running Benchmarks
------------------

The directory `Benchmarks` contains the files corresponding to the 1200 problems used in the experiments
(actually, the 28 problems not solved by `intuitR` and `intuit` within 600secs have been moved
into the subdirectory `_other_benckmarks_SYJ202`).

To run the benchmarks and get e report, from the directory
`script` run the commands `run_benchmarks.sh` and `build_report.sh`;
both commands need as parameter the timeout to be used (in seconds).
For instance, if the timeout is 600 secs run:

```console
 run_benchmarks.sh 600
 build_report.sh 600
```

Note that  command  `intuitR` must be in your PATH variable.
If you have installed [intuit](https://github.com/koengit/intuit),
the script also performs the tests with `intuit`.

To translate the benchmarks into
[fCube](http://www2.disco.unimib.it/fiorino/fcube.html) and
[IntHistGC](https://github.com/jessezwu/IntHistGC) syntax, run:

```console
 generate_fCube_benchmarks.sh
 generate_IntHistGC_benchmarks.sh
```

Both scripts invoke `intuitR`.

Experiments
-----------

The directory `timings` contains a detailed account of the
experiments we have performed with timeout 600 seconds on a machine 

```console
Intel(R) Core(TM) i7-8700 CPU @ 3.20GHz, 16GB memory
```
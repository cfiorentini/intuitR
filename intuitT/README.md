intuitT
=======

An implementation of  Claessen and Rosen `intuit` (https://github.com/koengit/intuit)
with the trace computations.

The installation and usage instructions are similar to `intuitR`:

- To install, from the directory  `intuitT` run

```console
    cabal install
```

- The input formula must be written in a text file using the
   [TPTP syntax](http://tptp.cs.miami.edu/TPTP/QuickGuide/Problems.html).
  To prove the formula in the file `form.p`, run one of the folllwing commands:

```console
     intuitT form.p         // only decide the validity 
     intuitT -t0 form.p     // minimum trace level, no output files 
     intuitT -t1 form.p     // medium  trace level, no output files 
     intuitT -t2 form.p     // maximum trace level, no output files 
     intuitT -t  form.p     // maximum trace level  with output files 
```

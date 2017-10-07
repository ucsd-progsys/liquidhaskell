Artifact for "Towards Complete Verification via SMT"
=======

# Online Demo 

The examples presented in Sections 2 and 3 of the paper can be viewed 
and checked at the online demo links below: 

- §2 Overview: [.html file](http://goto.ucsd.edu/~nvazou/popl18/_site/Overview.html), [.lhs source](https://raw.githubusercontent.com/ucsd-progsys/liquidhaskell/popl18/benchmarks/popl18/with_ple/Overview.lhs)
- §2.5 Laws for Lists: [.html file](http://goto.ucsd.edu/~nvazou/popl18/_site/LawsForLists.html), [.lhs source](https://raw.githubusercontent.com/ucsd-progsys/liquidhaskell/popl18/benchmarks/popl18/with_ple/LawsForLists.lhs) 
- §3.3 Natural Deduction: [.html file](http://goto.ucsd.edu/~nvazou/popl18/_site/NaturalDeduction.html), [lhs source](https://github.com/ucsd-progsys/liquidhaskell/blob/popl18/benchmarks/popl18/with_ple/NaturalDeduction.lhs)

# Running Benchmarks 

To run the benchmarks, you need to

1. **Get LiquidHaskell** via Docker or Source. 
2. **Run** the individual benchmarks.

## Build Option 1: Docker 

- Please install `docker` by following [this link](https://docs.docker.com/engine/installation/)


- Then, you can run the tests:
```
$ docker run -it parfunc/popl18-lh-prover-artifact
```
Or open an interactive shell:
```
$ docker run -it parfunc/popl18-lh-prover-artifact bash
```

## Build Option 2: Source 

You can install Liquid Haskell on your own machine from github. 

- **Step 1:** Download & Install:

    1. Install `z3` from [this link](https://github.com/Z3Prover/z3/releases).

    2. Install `stack` from [this link](https://docs.haskellstack.org/en/stable/README/).

    3. Clone and build LiquidHaskell:

```
$ git clone -b popl18 --recursive git@github.com:ucsd-progsys/liquidhaskell.git
$ cd liquidhaskell
$ stack install
```
    
    4. Clone the Benchmarks:
```
$ git clone -b popl18 --recursive https://github.com/iu-parfunc/verified-instances.git
$ git clone -b popl18 --recursive https://github.com/iu-parfunc/lvars.git
```

## Run Benchmarks

After getting LiquidHaskell and the benchmarks via the above,
you can now run LH on the benchmarks.

### Run Individual Files

Now you can run specific benchmarks in that shell, e.g. 
to check the files `Unification.hs` and `Solver.hs`, do:

```
$ stack exec -- liquid benchmarks/popl18/Overview.lhs
$ stack exec -- liquid benchmarks/popl18/LawsForLists.lhs
$ stack exec -- liquid benchmarks/popl18/NaturalDeduction.lhs
$ stack exec -- liquid benchmarks/popl18/ple/pos/Unification.hs
$ stack exec -- liquid benchmarks/popl18/ple/pos/Solver.hs
```

### Run Benchmarks

1. To run the benchmarks in categories "Arithmetic", "Class-Laws", "Higher-Order" and "Functional Correctness" _with_ and _without_ PLE respectively do:

```
$ cd liquidhaskell
$ stack test liquidhaskell --test-arguments="-p with_ple"  
$ stack test liquidhaskell --test-arguments="-p without_ple"
```

2. To run the benchmarks in "Conc. Sets" _with_ and _without_ PLE respectively do:

```
$ cd lvars ; make DOCKER=false TIMEIT=true PLE=true
$ cd lvars ; make DOCKER=false TIMEIT=true PLE=false
```

3. Finally, run the benchmarks in "n-body" & "Par. Reducers" categories, _with_ and _without_ PLE respectively do:

```
$ cd verified-instances ; make DOCKER=false TIMEIT=true PLE=true
$ cd verified-instances ; make DOCKER=false TIMEIT=true PLE=false
```

## Proof Size Measurements

To reproduce the proof sizes, do:

```
$ cd liquidhaskell
$ make count
```
```
$ cd verified-instances
$ make count
```
```
$ cd lvars
$ make count
```

You should see output that looks like:

```
src/Data/VerifiedEq/Instances/Sum.hs
CODE: 59
SPEC: 34
CODE + SPEC: 93
```

For each file `Foo.hs` we print:

* CODE = lines of haskell code (including proofs)
- i.e. the sum of the “Impl (l)” and “Proof (l)” columns from Table  1
(we have to partition the two by manual inspection as, after all all the motivation of the paper is that proofs are just code!)


* SPEC = lines of theorem specifications (including liquid & haskell sigs)
- i.e. the the “Spec (l)” column of Table 1


# Benchmark Listing 

The benchmarks described in the paper are located as follows:

* Arithmetic     :
	- With-PLE
		- [benchmarks/popl18/with_ple/Fibonacci.hs](https://raw.githubusercontent.com/ucsd-progsys/liquidhaskell/popl18/benchmarks/popl18/with_ple/Fibonacci.hs)
		- [benchmarks/popl18/with_ple/Ackermann.hs](https://raw.githubusercontent.com/ucsd-progsys/liquidhaskell/popl18/benchmarks/popl18/with_ple/Fibonacci.hs)

	- Without-PLE
		- [benchmarks/popl18/without_ple/Fibonacci.hs](https://raw.githubusercontent.com/ucsd-progsys/liquidhaskell/popl18/benchmarks/popl18/with_ple/Fibonacci.hs)
		- [benchmarks/popl18/without_ple/Ackermann.hs](https://raw.githubusercontent.com/ucsd-progsys/liquidhaskell/popl18/benchmarks/popl18/with_ple/Fibonacci.hs)

* Higher-Order   :
	- With-PLE
		- [benchmarks/popl18/with_ple/NaturalDeduction.hs](https://raw.githubusercontent.com/ucsd-progsys/liquidhaskell/popl18/benchmarks/popl18/with_ple/Fibonacci.hs)
		- [benchmarks/popl18/with_ple/FoldrUniversal.hs](https://raw.githubusercontent.com/ucsd-progsys/liquidhaskell/popl18/benchmarks/popl18/with_ple/Fibonacci.hs)

	- Without-PLE
		- [benchmarks/popl18/without_ple/NaturalDeduction.hs](https://raw.githubusercontent.com/ucsd-progsys/liquidhaskell/popl18/benchmarks/popl18/with_ple/Fibonacci.hs)
		- [benchmarks/popl18/without_ple/FoldrUniversal.hs](https://raw.githubusercontent.com/ucsd-progsys/liquidhaskell/popl18/benchmarks/popl18/with_ple/Fibonacci.hs)

* Class-Laws     :
	- With-PLE
		- [benchmarks/popl18/with_ple/pos/MonoidMaybe.hs](https://raw.githubusercontent.com/ucsd-progsys/liquidhaskell/popl18/benchmarks/popl18/with_ple/Fibonacci.hs)
		- [benchmarks/popl18/with_ple/pos/MonoidList.hs](https://raw.githubusercontent.com/ucsd-progsys/liquidhaskell/popl18/benchmarks/popl18/with_ple/Fibonacci.hs)
		- [benchmarks/popl18/with_ple/pos/FunctorMaybe.hs](https://raw.githubusercontent.com/ucsd-progsys/liquidhaskell/popl18/benchmarks/popl18/with_ple/Fibonacci.hs)
		- [benchmarks/popl18/with_ple/pos/FunctorId.hs](https://raw.githubusercontent.com/ucsd-progsys/liquidhaskell/popl18/benchmarks/popl18/with_ple/Fibonacci.hs)
		- [benchmarks/popl18/with_ple/pos/FunctorList.hs](https://raw.githubusercontent.com/ucsd-progsys/liquidhaskell/popl18/benchmarks/popl18/with_ple/Fibonacci.hs)
		- [benchmarks/popl18/with_ple/pos/ApplicativeMaybe.hs](https://raw.githubusercontent.com/ucsd-progsys/liquidhaskell/popl18/benchmarks/popl18/with_ple/Fibonacci.hs)
		- [benchmarks/popl18/with_ple/pos/ApplicativeList.hs](https://raw.githubusercontent.com/ucsd-progsys/liquidhaskell/popl18/benchmarks/popl18/with_ple/Fibonacci.hs)
		- [benchmarks/popl18/with_ple/pos/ApplicativeId.hs](https://raw.githubusercontent.com/ucsd-progsys/liquidhaskell/popl18/benchmarks/popl18/with_ple/Fibonacci.hs)
		- [benchmarks/popl18/with_ple/pos/MonadMaybe.hs](https://raw.githubusercontent.com/ucsd-progsys/liquidhaskell/popl18/benchmarks/popl18/with_ple/Fibonacci.hs)
		- [benchmarks/popl18/with_ple/pos/MonadList.hs](https://raw.githubusercontent.com/ucsd-progsys/liquidhaskell/popl18/benchmarks/popl18/with_ple/Fibonacci.hs)
		- [benchmarks/popl18/with_ple/pos/MonadId.hs](https://raw.githubusercontent.com/ucsd-progsys/liquidhaskell/popl18/benchmarks/popl18/with_ple/Fibonacci.hs)

	- Without-PLE
		- [benchmarks/popl18/without_ple/pos/MonoidMaybe.hs](https://raw.githubusercontent.com/ucsd-progsys/liquidhaskell/popl18/benchmarks/popl18/without_ple/pos/MonoidMaybe.hs)
		- [benchmarks/popl18/without_ple/pos/MonoidList.hs](https://raw.githubusercontent.com/ucsd-progsys/liquidhaskell/popl18/benchmarks/popl18/without_ple/pos/MonoidList.hs)
		- [benchmarks/popl18/without_ple/pos/FunctorMaybe.hs](https://raw.githubusercontent.com/ucsd-progsys/liquidhaskell/popl18/benchmarks/popl18/without_ple/pos/FunctorMaybe.hs)
		- [benchmarks/popl18/without_ple/pos/FunctorId.hs](https://raw.githubusercontent.com/ucsd-progsys/liquidhaskell/popl18/benchmarks/popl18/without_ple/pos/FunctorId.hs)
		- [benchmarks/popl18/without_ple/pos/FunctorList.hs](https://raw.githubusercontent.com/ucsd-progsys/liquidhaskell/popl18/benchmarks/popl18/without_ple/pos/FunctorList.hs)
		- [benchmarks/popl18/without_ple/pos/ApplicativeMaybe.hs](https://raw.githubusercontent.com/ucsd-progsys/liquidhaskell/popl18/benchmarks/popl18/without_ple/pos/ApplicativeMaybe.hs)
		- [benchmarks/popl18/without_ple/pos/ApplicativeList.hs](https://raw.githubusercontent.com/ucsd-progsys/liquidhaskell/popl18/benchmarks/popl18/without_ple/pos/ApplicativeList.hs)
		- [benchmarks/popl18/without_ple/pos/ApplicativeId.hs](https://raw.githubusercontent.com/ucsd-progsys/liquidhaskell/popl18/benchmarks/popl18/without_ple/pos/ApplicativeId.hs)
		- [benchmarks/popl18/without_ple/pos/MonadMaybe.hs](https://raw.githubusercontent.com/ucsd-progsys/liquidhaskell/popl18/benchmarks/popl18/without_ple/pos/MonadMaybe.hs)
		- [benchmarks/popl18/without_ple/pos/MonadList.hs](https://raw.githubusercontent.com/ucsd-progsys/liquidhaskell/popl18/benchmarks/popl18/without_ple/pos/MonadList.hs)
		- [benchmarks/popl18/without_ple/pos/MonadId.hs](https://raw.githubusercontent.com/ucsd-progsys/liquidhaskell/popl18/benchmarks/popl18/without_ple/pos/MonadId.hs)

* Func. Correct. : 
	- With-PLE
		- [benchmarks/popl18/with_ple/pos/Solver.hs](https://raw.githubusercontent.com/ucsd-progsys/liquidhaskell/popl18/benchmarks/popl18/with_ple/pos/Solver.hs)
		- [benchmarks/popl18/with_ple/pos/Unification.hs](https://raw.githubusercontent.com/ucsd-progsys/liquidhaskell/popl18/benchmarks/popl18/with_ple/pos/Unification.hs)

	- Without-PLE
		- [benchmarks/popl18/without_ple/pos/Solver.hs](https://raw.githubusercontent.com/ucsd-progsys/liquidhaskell/popl18/benchmarks/popl18/without_ple/pos/Solver.hs)
		- [benchmarks/popl18/without_ple/pos/Unification.hs](https://raw.githubusercontent.com/ucsd-progsys/liquidhaskell/popl18/benchmarks/popl18/without_ple/pos/Unification.hs)


* Conc-Sets:
	- With-PLE
		- [src/lvish/tests/verified/Sum.hs](https://raw.githubusercontent.com/iu-parfunc/lvars/popl18/src/lvish/tests/verified/Sum.hs)

	- Without-PLE
		- [src/lvish/tests/verified/SumNoPLE.hs](https://raw.githubusercontent.com/iu-parfunc/lvars/popl18/src/lvish/tests/verified/SumNoPLE.hs)

* N-Body: 
	- With-PLE
		- [examples/nbody/allpairs_verified.hs ](https://raw.githubusercontent.com/iu-parfunc/verified-instances/popl18/examples/nbody/allpairs_verified.hs)

	- Without-PLE
		- [examples/nbody/allpairs_verifiedNoPLE.hs ](https://raw.githubusercontent.com/iu-parfunc/verified-instances/popl18/examples/nbody/allpairs_verifiedNoPLE.hs)

* Par-Reducers   :
	- With-PLE
		- [examples/dpj/IntegerSumReduction2.hs](https://raw.githubusercontent.com/iu-parfunc/verified-instances/popl18/examples/dpj/IntegerSumReduction2.hs)

	- Without-PLE
		- [examples/dpj/IntegerSumReduction2NoPLE.hs](https://raw.githubusercontent.com/iu-parfunc/verified-instances/popl18/examples/dpj/IntegerSumReduction2NoPLE.hs)

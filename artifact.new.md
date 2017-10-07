# Artifact for "Towards Complete Verification via SMT"

The paper presents how we extended Liquid Haskell 
to allow complete verification via SMTs.
You can run Liquid Haskell online, 
using a docker VM, *or* 
build it from source.
This artifact describes

- [Online Demo:](#online) How to run online the examples presented in the paper. 
- [Running Benchmarks:](#benchmarks) How to run the banchmarks of Table 1 of the paper.
- [Source Files:](#source-files) How to check the source files of the benchmarks of Table 1.



## <a name="online"></a> Online Demo


The examples presented in the paper (Sections 2 and 3) can be viewed 
and checked at the interactive, online demo links below: 


We provide interactive Liquid Haksell code for 
the examples presented in Sections 2 and 3 of the paper. 
The Liquid Haskell queries are checked by sending requests to 
the Liquid Haskell server hosted at [http://goto.ucsd.edu:8090/](http://goto.ucsd.edu:8090/).

- §2 Overview: [.html file](http://goto.ucsd.edu/~nvazou/popl18/_site/Overview.html), [.lhs source](https://raw.githubusercontent.com/ucsd-progsys/liquidhaskell/popl18/benchmarks/popl18/with_ple/Overview.lhs)
- §2.5 Laws for Lists: [.html file](http://goto.ucsd.edu/~nvazou/popl18/_site/LawsForLists.html), [.lhs source](https://raw.githubusercontent.com/ucsd-progsys/liquidhaskell/popl18/benchmarks/popl18/with_ple/LawsForLists.lhs) 
- §3.3 Natural Deduction: [.html file](http://goto.ucsd.edu/~nvazou/popl18/_site/NaturalDeduction.html), [lhs source](https://raw.githubusercontent.com/ucsd-progsys/liquidhaskell/popl18/benchmarks/popl18/with_ple/NaturalDeduction.lhs)


## <a name="benchmarks"></a> Running Benchmarks

To run the benchmarks, you can

1. Use a Docker image 
2. Install Liquid Haskell from source [preferred]


### Build Option 1: Docker 

- Please install `docker`. 

- Then, you can run the tests:

    ```
    $ docker run -it parfunc/popl18-lh-prover-artifact
    ```

    Or open an interactive shell:

    ```
    $ docker run -it parfunc/popl18-lh-prover-artifact bash
    ```

### Build Option 2: Source 

You can install Liquid Haskell on your own machine from github. 

#### Download & Install:

1. Install `z3` from [this link](https://github.com/Z3Prover/z3/releases).

2. Install `stack` from [this link](https://docs.haskellstack.org/en/stable/README/).

3. Clone and build LiquidHaskell:

    ```
    $ git clone -b popl18 --recursive git@github.com:ucsd-progsys/liquidhaskell.git
    ```

    ```
    $ cd liquidhaskell
    ```
        
    ```
    $ stack install
    ```
    
4. Clone the Benchmarks:

    ```
    $ git clone -b popl18 --recursive https://github.com/iu-parfunc/verified-instances.git
    ```

    ```
    $ git clone -b popl18 --recursive https://github.com/iu-parfunc/lvars.git
    ```

#### Run Benchmarks

After getting Liquid Haskell and the benchmarks via the above,
you can now run Liquid Haskell on the benchmarks.

##### Run Individual Files

Now you can run specific benchmarks in that shell, e.g. 
to check the files `Unification.hs` and `Solver.hs`, do:


    $ stack exec -- liquid benchmarks/popl18/Overview.lhs
    $ stack exec -- liquid benchmarks/popl18/LawsForLists.lhs
    $ stack exec -- liquid benchmarks/popl18/NaturalDeduction.lhs
    $ stack exec -- liquid benchmarks/popl18/ple/pos/Unification.hs
    $ stack exec -- liquid benchmarks/popl18/ple/pos/Solver.hs

##### Run All the Benchmarks of Table 1

We split the benchmarks of Table 1 to 3 categories.


1. To run the benchmarks in categories "Arithmetic", "Class-Laws", "Higher-Order", and "Functional Correctness" of Table 1 _with_ PLE _with_ and _without_ PLE, respectively, do:

    $ cd liquidhaskell

    $ stack test liquidhaskell --test-arguments="-p with_ple"
    
    $ stack test liquidhaskell --test-arguments="-p without_ple"


2. To run the benchmarks in "Conc. Sets" _with_ and _without_ PLE, respectively, do:

    $ cd lvars ; make DOCKER=false TIMEIT=true PLE=true

    $ cd lvars ; make DOCKER=false TIMEIT=true PLE=false


3. Finally, run the benchmarks in "n-body" & "Par. Reducers" categories, _with_ and _without_ PLE, respectively, do:

    $ cd verified-instances ; make DOCKER=false TIMEIT=true PLE=true

    $ cd verified-instances ; make DOCKER=false TIMEIT=true PLE=false



## <a name="source-files"></a>Source Files 

The source files of Benchmarks in Table 1 can be located as follows.

<style>
table {
    border-collapse: collapse;
    font-family: arial, sans-serif;
    text-align: left;
}

td, th {
    border: 1px solid #dddddd;
    border-collapse: collapse;
    text-align: left;
}
</style>

<table>
  <tr>
    <th>Category</th>
    <th><i>Without</i> PLE Search&nbsp;&nbsp;</th>
    <th><i>With</i> PLE Search&nbsp;&nbsp;</th>
  </tr>
  <tr>
    <td>Arithmetic</td>
    <td><a target="_blank" href="https://raw.githubusercontent.com/ucsd-progsys/liquidhaskell/popl18/benchmarks/popl18/without_ple/pos/Fibonacci.hs">Fibonacci.hs</a></td>
    <td><a target="_blank" href="https://raw.githubusercontent.com/ucsd-progsys/liquidhaskell/popl18/benchmarks/popl18/with_ple/pos/Fibonacci.hs">Fibonacci.hs</a></td>
  </tr>
  <tr>
    <td></td>
    <td><a target="_blank" href="https://raw.githubusercontent.com/ucsd-progsys/liquidhaskell/popl18/benchmarks/popl18/without_ple/pos/Ackermann.hs">Ackermann.hs</a></td>
    <td><a target="_blank" href="https://raw.githubusercontent.com/ucsd-progsys/liquidhaskell/popl18/benchmarks/popl18/with_ple/pos/Ackermann.hs">Ackermann.hs</a></td>
  </tr>
  <tr>
    <td>Class Laws</td>
    <td><a target="_blank" href="https://raw.githubusercontent.com/ucsd-progsys/liquidhaskell/popl18/benchmarks/popl18/without_ple/pos/MonoidMaybe.hs">MonoidMaybe.hs</a></td>
    <td><a target="_blank" href="https://raw.githubusercontent.com/ucsd-progsys/liquidhaskell/popl18/benchmarks/popl18/with_ple/pos/MonoidMaybe.hs">MonoidMaybe.hs</a></td>
  </tr>
  <tr>
    <td></td>
    <td><a target="_blank" href="https://raw.githubusercontent.com/ucsd-progsys/liquidhaskell/popl18/benchmarks/popl18/without_ple/pos/MonoidList.hs">MonoidList.hs</a></td>
    <td><a target="_blank" href="https://raw.githubusercontent.com/ucsd-progsys/liquidhaskell/popl18/benchmarks/popl18/with_ple/pos/MonoidList.hs">MonoidList.hs</a></td>
  </tr>
  <tr>
    <td></td>
    <td><a target="_blank" href="https://raw.githubusercontent.com/ucsd-progsys/liquidhaskell/popl18/benchmarks/popl18/without_ple/pos/FunctorId.hs">FunctorId.hs</a></td>
    <td><a target="_blank" href="https://raw.githubusercontent.com/ucsd-progsys/liquidhaskell/popl18/benchmarks/popl18/with_ple/pos/FunctorId.hs">FunctorId.hs</a></td>
  </tr>
  <tr>
    <td></td>
    <td><a target="_blank" href="https://raw.githubusercontent.com/ucsd-progsys/liquidhaskell/popl18/benchmarks/popl18/without_ple/pos/FunctorMaybe.hs">FunctorMaybe.hs</a></td>
    <td><a target="_blank" href="https://raw.githubusercontent.com/ucsd-progsys/liquidhaskell/popl18/benchmarks/popl18/with_ple/pos/FunctorMaybe.hs">FunctorMaybe.hs</a></td>
  </tr>
  <tr>
    <td></td>
    <td><a target="_blank" href="https://raw.githubusercontent.com/ucsd-progsys/liquidhaskell/popl18/benchmarks/popl18/without_ple/pos/FunctorList.hs">FunctorList.hs</a></td>
    <td><a target="_blank" href="https://raw.githubusercontent.com/ucsd-progsys/liquidhaskell/popl18/benchmarks/popl18/with_ple/pos/FunctorList.hs">FunctorList.hs</a></td>
  </tr>
  <tr>
    <td></td>
    <td><a target="_blank" href="https://raw.githubusercontent.com/ucsd-progsys/liquidhaskell/popl18/benchmarks/popl18/without_ple/pos/ApplicativeId.hs">ApplicativeId.hs</a></td>
    <td><a target="_blank" href="https://raw.githubusercontent.com/ucsd-progsys/liquidhaskell/popl18/benchmarks/popl18/with_ple/pos/ApplicativeId.hs">ApplicativeId.hs</a></td>
  </tr>
  <tr>
    <td></td>
    <td><a target="_blank" href="https://raw.githubusercontent.com/ucsd-progsys/liquidhaskell/popl18/benchmarks/popl18/without_ple/pos/ApplicativeMaybe.hs">ApplicativeMaybe.hs</a></td>
    <td><a target="_blank" href="https://raw.githubusercontent.com/ucsd-progsys/liquidhaskell/popl18/benchmarks/popl18/with_ple/pos/ApplicativeMaybe.hs">ApplicativeMaybe.hs</a></td>
  </tr>
  <tr>
    <td></td>
    <td><a target="_blank" href="https://raw.githubusercontent.com/ucsd-progsys/liquidhaskell/popl18/benchmarks/popl18/without_ple/pos/ApplicativeList.hs">ApplicativeList.hs</a></td>
    <td><a target="_blank" href="https://raw.githubusercontent.com/ucsd-progsys/liquidhaskell/popl18/benchmarks/popl18/with_ple/pos/ApplicativeList.hs">ApplicativeList.hs</a></td>
  </tr>
  <tr>
    <td></td>
    <td><a target="_blank" href="https://raw.githubusercontent.com/ucsd-progsys/liquidhaskell/popl18/benchmarks/popl18/without_ple/pos/MonadId.hs">MonadId.hs</a></td>
    <td><a target="_blank" href="https://raw.githubusercontent.com/ucsd-progsys/liquidhaskell/popl18/benchmarks/popl18/with_ple/pos/MonadId.hs">MonadId.hs</a></td>
  </tr>
  <tr>
    <td></td>
    <td><a target="_blank" href="https://raw.githubusercontent.com/ucsd-progsys/liquidhaskell/popl18/benchmarks/popl18/without_ple/pos/MonadMaybe.hs">MonadMaybe.hs</a></td>
    <td><a target="_blank" href="https://raw.githubusercontent.com/ucsd-progsys/liquidhaskell/popl18/benchmarks/popl18/with_ple/pos/MonadMaybe.hs">MonadMaybe.hs</a></td>
  </tr>
  <tr>
    <td></td>
    <td><a target="_blank" href="https://raw.githubusercontent.com/ucsd-progsys/liquidhaskell/popl18/benchmarks/popl18/without_ple/pos/MonadList.hs">MonadList.hs</a></td>
    <td><a target="_blank" href="https://raw.githubusercontent.com/ucsd-progsys/liquidhaskell/popl18/benchmarks/popl18/with_ple/pos/MonadList.hs">MonadList.hs</a></td>
  </tr>
  <tr>
    <td>Higher-Order</td>
    <td><a target="_blank" href="https://raw.githubusercontent.com/ucsd-progsys/liquidhaskell/popl18/benchmarks/popl18/without_ple/pos/FoldrUniversal.hs">FoldrUniversal.hs</a></td>
    <td><a target="_blank" href="https://raw.githubusercontent.com/ucsd-progsys/liquidhaskell/popl18/benchmarks/popl18/with_ple/pos/FoldrUniversal.hs">FoldrUniversal.hs</a></td>
  </tr>
  <tr>
    <td></td>
    <td><a target="_blank" href="https://raw.githubusercontent.com/ucsd-progsys/liquidhaskell/popl18/benchmarks/popl18/without_ple/pos/NaturalDeduction.hs">NaturalDeduction.hs</a></td>
    <td><a target="_blank" href="https://raw.githubusercontent.com/ucsd-progsys/liquidhaskell/popl18/benchmarks/popl18/with_ple/pos/NaturalDeduction.hs">NaturalDeduction.hs</a></td>
  </tr>
  <tr>
    <td>Func. Correct</td>
    <td><a target="_blank" href="https://raw.githubusercontent.com/ucsd-progsys/liquidhaskell/popl18/benchmarks/popl18/without_ple/pos/Solver.hs">Solver.hs</a></td>
    <td><a target="_blank" href="https://raw.githubusercontent.com/ucsd-progsys/liquidhaskell/popl18/benchmarks/popl18/with_ple/pos/Solver.hs">Solver.hs</a></td>
  </tr>
  <tr>
    <td></td>
    <td><a target="_blank" href="https://raw.githubusercontent.com/ucsd-progsys/liquidhaskell/popl18/benchmarks/popl18/without_ple/pos/Unification.hs">Unification.hs</a></td>
    <td><a target="_blank" href="https://raw.githubusercontent.com/ucsd-progsys/liquidhaskell/popl18/benchmarks/popl18/with_ple/pos/Unification.hs">Unification.hs</a></td>
  </tr>
  <tr>
    <td> Conc-Sets</td>
    <td><a target="_blank" href="https://raw.githubusercontent.com/iu-parfunc/lvars/popl18/src/lvish/tests/verified/SumNoPLE.hs">SumNoPLE.hs</a></td>
    <td><a target="_blank" href="https://raw.githubusercontent.com/iu-parfunc/lvars/popl18/src/lvish/tests/verified/Sum.hs">Sum.hs</a></td>
  </tr>
  <tr>
    <td> N-Body</td>
    <td><a target="_blank" href="https://raw.githubusercontent.com/iu-parfunc/verified-instances/popl18/examples/nbody/allpairs_verifiedNoPLE.hs">allpairs_verifiedNoPLE.hs</a></td>
    <td><a target="_blank" href="https://raw.githubusercontent.com/iu-parfunc/verified-instances/popl18/examples/nbody/allpairs_verified.hs">allpairs_verified.hs</a></td>
  </tr>
  <tr>
    <td> Par-Reducers&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;</td>
    <td><a target="_blank" href="https://raw.githubusercontent.com/iu-parfunc/verified-instances/popl18/examples/dpj/IntegerSumReduction2NoPLE.hs">IntegerSumReduction2NoPLE.hs</a>&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;</td>
    <td><a target="_blank" href="https://raw.githubusercontent.com/iu-parfunc/verified-instances/popl18/examples/dpj/IntegerSumReduction2.hs">IntegerSumReduction2.hs</a></td>
  </tr>
</table>


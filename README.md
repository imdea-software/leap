
# README for LEAP

<b>NOTE:</b> this version of LEAP is still experimental, documentation may be out of date.


## Introduction:

LEAP is a prototype theorem prover which aims the formal verification of temporal properties, both <b>safety</b> and <b>liveness</b>, of parametrized programs. In particular, LEAP is designed for the analysis of programs that manipulate concurrent data types that store both finite and infinite data.

LEAP receives as input an annotated program and a temporal specification. As output, it states whether the temporal specification holds under the assumption of <b>an unbounded number of threads</b> executing the input program. To accomplish this, in its core LEAP implements:

+ A collection of specialized deductive proof rules which reduce the verification problem to a finite collection of verification conditions, whose validity entails the satisfaction of the temporal specification by the parametrized system.

+ A set of decision procedures, which can automatically verify the validity of the previously generated verification conditions.


## Installation:

LEAP is available as source code and as binaries for Linux and Mac. Since LEAP works of top of some SMT solvers, you will need to install at least:
+ <a href="http://yices.csl.sri.com/old/download-yices1-full.shtml">Yices</a>
+ <a href="https://github.com/Z3Prover/z3">Z3</a>

### Compiling this repository:

+ Get the source code `git clone https://github.com/imdea-software/leap`
+ Compile LEAP `make leap` (*requires ocamlbuild and ocaml >= 4.02.0*)


### Examples, tutorials and binaries:

Examples, tutorials and compiled binaries for Linux and Mac are available from <a href="http://software.imdea.org/leap/">LEAP's website</a>. In particular, there exists binary versions for:
+ <a href="http://software.imdea.org/leap/downloads/leap_linux-32_0.2">32-bits Linux</a>
+ <a href="http://software.imdea.org/leap/downloads/leap_linux-64_0.2">64-bits Linux</a>
+ <a href="http://software.imdea.org/leap/downloads/leap_mac_0.2">Max OSX</a>

Examples can also be found in the [examples](./examples) folder of this repository.


### Online tool:

<b>NEW!</b> LEAP can now be used at its <a href="http://ares.software.imdea.org/leap">online website</a>.


## Usage:

There exists a <a href="http://software.imdea.org/leap/tutorial.html">tutorial</a> at LEAP's website.

It is possible to check whether LEAP was successfully installed by executing `leap -version`, which output the current LEAP version.
A list of available options can be obtained by executing `leap -help`. Further details about command line options and the methodology for using LEAP can be found in the [examples](./examples) folder of this repository and in chapter 9 of <a href="http://software.imdea.org/~asanchez/papers/asanchez-phd.pdf">Alejandro Sanchez's PhD Thesis</a>.


## Related publications:

A comprehensive presentation of LEAP can be found in chapter 9 of <a href="http://software.imdea.org/~asanchez/papers/asanchez-phd.pdf">Alejandro Sanchez's PhD Thesis</a>.

LEAP implementation is based on the following publications:

+ <a href="http://software.imdea.org/~asanchez/papers/2015/sanchez15parametrized.pdf">Parametrized Invariance for Infinite State Processes</a>, which introduces the parametrized invariance proof rules for safety properties (_Acta Informatica 2015_).
+ <a href="http://software.imdea.org/~asanchez/papers/2014/sanchez14parametrized.pdf">Parametrized Verification Diagrams</a>, which describes a diagram based method which enables the parametrized verification of liveness properties (_TIME 2014_).
+ <a href="http://software.imdea.org/~asanchez/papers/2014/sanchez14leap.pdf">LEAP: A Tool for the Parametrized Verification of Concurrent Datatypes</a>, which briefly introduces the functionalities offered by LEAP (_CAV 2014_).
+ <a href="http://software.imdea.org/~asanchez/papers/2014/sanchez14formal.pdf">Formal Verification of Skiplists with Arbitrarily Many Levels</a>, which describes a decision procedure for skiplists with an unbounded number of levels (_ATVA 2014_).
+ <a href="http://software.imdea.org/~asanchez/papers/2011/sanchez11theory.pdf">A Theory of Skiplists with Applications to the Verification of Concurrent Datatypes</a>, which presents a decision procedure for families of skiplists with a bounded number of levels (_NFM 2011_).
+ <a href="http://software.imdea.org/~asanchez/papers/2010/sanchez10decision.pdf">Decision Procedures for the Temporal Verification of Concurrent Lists</a>, which describes a decision procedure for data structures of the shape of concurrent lists (_ICFEM 2010_).

## Contact:

LEAP is currently developed and maintained by:

+ <a href="http://software.imdea.org/~asanchez">Alejandro Sánchez</a> (<a href="https://github.com/alesanz">@alesanz</a>)
+ <a href="http://software.imdea.org/~cesar/">César Sánchez</a> (<a href="https://github.com/cesar-sanchez">@cesar-sanchez</a>)

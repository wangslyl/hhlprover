# hhlprover
======================================================================    
An Improved HHL Prover: An Interactive Theorem Prover for Hybrid Systems

Validated on platform: 32/64bit-Ubuntu-Desktop-14.04/14.10 

Corresponding e-mail: wangsl@ios.ac.cn
======================================================================    	


1. Extract the file, which should create the structure

   /HHLProver_SD
   /HHLProver_SD/CaseStudies/HCS
   /HHLProver_SD/HHLProver
   /HHLProver_SD/QEInvGenerator
   /HHLProver_SD/SOSInvGenerator
   /HHLProver_SD/README.md

2. Install the required tools and libraries

a. Isabelle/HOL (validated after R2014)
	http://isabelle.in.tum.de/

b. Mathematica (validated in R10)
	http://www.wolfram.com/mathematica/

c. Matlab (validated in R2012a~R2014a, with Simulink bundled)
	http://www.mathworks.com/products/matlab/

d. Yalmip (remember to add paths in your MATLAB path)
	http://users.isy.liu.se/johanl/yalmip/

e. SDPT3
	http://www.math.nus.edu.sg/~mattohkc/sdpt3.html

3. Set environment variables

   $ export HHLProverSDHOME=".../HHLProver_SD"
   $ export MATLABHOME=".../Matlab_R2014a/bin"
   $ export MATHEMATICAHOME=".../Mathematica10/Executables"

4. Demonstration on case study HCS

		open $HHLProverSDHOME/CaseStudies/HCS/lunarlander/goal.thy or
		     $HHLProverSDHOME/CaseStudies/HCS/lunarlander/goal.thy
		in Isabelle. Click 'Yes' to load required files,
		specify the degree of invariant template, for example 6, in the pop-up terminal.

        The proof will be completed when you see "No subgoals!" in Isabelle.

=========================================================================================================

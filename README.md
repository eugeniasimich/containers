# Formalisation of Containers
Graduate thesis to obtain the Master degree in Computer Science  
[Departamento de Ciencias de la computación](https://www.fceia.unr.edu.ar/lcc/), [Universidad Nacional de Rosario](http://www.unr.edu.ar/)  
Author: Eugenia Simich  
Supervisor: [Mauro Jaskelioff](http://www.fceia.unr.edu.ar/~mauro/)  

## Overview of the project
  The present library extends the container section of Agda standard library. The `Category` folder includes all the categorical formalizations needed, including the notion of product, coproduct, exponential, initial and terminal object. In the `Container` folder instances of these constructions and proofs of their correctness are given. 

  In the directory `doc` you will find the complete graduate thesis text -in spanish-, compilable doing `make`. For the compilation to succeed, you will need the following packages installed:

  * Agda v2.5.1 or later
  * [Latex](https://www.latex-project.org/get/)
  * [babelbib](https://www.ctan.org/pkg/babelbib) latex package
  * [catchfilebetweentags](https://www.ctan.org/pkg/catchfilebetweentags) latex package

To tell the Makefile where your Agda standard library is, just copy the file `agda_stdlib.mk.example` to `agda_stdlib.mk`, filling in the path.
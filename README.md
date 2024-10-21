# Double Auctions: Formalization and Automated Checkers

## Introduction.

This folder contains the coq formalization of double auctions. 

Double auction is used in the financial markets by exchanges for trading between multiple buyers with multiple sellers. 
For example, a specif type of double auction, known as call auction, is used for price discovery (opening price) at several stock exchanges all over the world. 
In this formalization, we have modeled and formalized various properties of call auctions along with their algorithms. 
We extract certified OCaml and Haskell programs for matching buyers with sellers at the stock exchange during double auction session.
We also include a demonstration of our automated checker on real market data that uses the extracted OCaml programs. 

## How to compile the Coq formalization:

To compile the formalization please run the executable shell script:
> sh run.sh

This file may take 5-6 minutes to compile.

## How to run the demonstration:

After compiling the Coq code, go to the demonstration folder and run the following command:
> sh CompileAndRunAll.sh

The details of the demonstration are in the README file of the Demonstration folder.

## Coq files details:  

1. The main lemmas for the correctness of fairness are in the file FAIR.v
2. The UM process and its correctness theorems are in UM.v. The UM process is used at the exchanges.
3. For MM process, go to the file MM.v.
4. The Demand_suppy_Inequality.v file contains combinatorial results on matchings. 
5. The Uniqueness.v file contains uniqueness-related results.
6. All the final results are available in the file Demo.v. 

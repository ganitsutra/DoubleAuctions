# DoubleAuctions
Double Auctions: Formalization and Automated Checkers

#Introduction.

This folder contains the coq formalization of double auctions. 

Double auction is used in the financial markets by exchanges for trading between multiple buyers with multiple sellers. 
For example, a specif type of double auction, known as call auction, is used for price discovery (opening price) at several stock exchanges all over the world. 
In this formalization, we have modeled and formalized various properties of call auctions along with their algorithms. 
We extract a certified OCaml, Haskell program for matching buyers with sellers at the stock exchange during double auction session.
We also have demonstrated our extracted OCaml programs on real market data. Please see the directory Demonstration.

#How to use the coq formalization: To compile the code please run the executable shell script run.sh

# Coq files details: We have formalized matching at the financial exchanges. 
0. All the important results, processes, and programs are extracted in Demo.v file. To run this file, please 
run run.sh file from your terminal ($ ./run.sh or $ sh run.sh ). This file may take 5-6 minutes to compile. 
Once run.sh is completed, please run "coqc Demo.v" from your terminal. In short, 
type the following command from your terminal:

> ./auction.sh;
> coqc Demo.v 

1. The main lemmas for the correctness of fairness are in the file FAIR.v
2. The UM process and its correctness theorems are in UM.v. The UM process is used at the exchanges.
3. For MM process, go to the file MM.v.
4. The Demand_suppy_Inequality.v file contains combinatorial results on matchings. 
5. The Uniqueness.v file contains uniqueness-related results.

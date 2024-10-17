#!/bin/bash

ocamlc -c certified.mli 
ocamlc -I +str -o create certified.ml Print.ml Create.ml
./create

ocamlc -c certified.mli
ocamlc -I +str -o compare certified.ml Print.ml Compare.ml
./compare

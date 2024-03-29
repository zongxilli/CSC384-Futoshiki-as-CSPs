﻿# CSC384-Futoshiki-as-CSPs
University of Toronto CSC384(Introduction to Artificial Intelligence) Assignment 3

Forward Checking constraint propagator & Generalized Arc Consistence (GAC) constraint propagator
2 models for solving futoshiki

## Introduction
There are two parts to this assignment

the implementation of two constraint propagators – a Forward Checking constraint propagator, and a Generalized Arc Consistence (GAC) constraint propagator,

the encoding of two different CSP models to solve the logic puzzle, Futoshiki, as described below. In one model you will use only binary not-equal constraints, while in the other model you will use 9-ary all-different constraints in addition to binary not-equal constraints.

### What is supplied:

cspbase.py – class definitions for the python objects Constraint, Variable, and BT.

propagators.py - starter code for the implementation of your two propagators. You will modify this file with the addition of two new procedures prop_FC and prop_GAC , to realize Forward Checking and GAC, respectively.

futoshiki_csp.py – starter code for the two Futoshiki CSP models.

Sample test cases (in automarker.py)  for testing your code. 

You can download all of the starter code at this link. download

## Futoshiki Formal Description
The Futoshiki puzzle 1 has the following formal description:  (from this source (Links to an external site.)):
The puzzle is played on a grid board with dimensions n rows by n columns. The board is always a square.

The board has n2 spaces on it, where each space may take a value between 1 and n inclusive. You will use a list of lists in order to represent assigned values to the variables on this grid.
The start state of the puzzle may have some spaces already filled in.  
Ad ditionally, the starting board may have some inequality constraints specified between some of the spaces. These inequality constraints will only apply to two cells that are horizontally adjacent to one another, i.e. the constraints will only apply to rows and not columns. If there is no inequality constraint between two adjacent cells, this will be represented with a dot (i.e., with a ‘.’). For example, consider this 2 x 2 board: [[ 0 ,<, 0 , ] , [ 0 ,., 0 ]] . The assignments [[ 1 ,<, 2 , ] , [ 2 ,., 1 ]] would satisfy the inequality constraint.
A  puzzle is solved if:
Every space on the board is given one value between 1 and n inclusive.
All specified inequality constraints are satisfied.
No row contains more than one of the same number.
No column contains more than one of the same number.
An example of a Futoshiki instance and its solution are depicted in figure 1. You can also play Futoshiki online (at https://www.futoshiki.org/ (Links to an external site.)) but note that column inequality constraints might be included in the games you find here.

## Question 1: Propagators (worth 60/100 marks)
You will implement python functions to realize two constraint propagators – a Forward Checking constraint propagator and a Generalized Arc Consistence (GAC) constraint propagator. These propagators are briefly described below. The files cspbase.py and propagators.py provide the complete input/output specification of the functions you are to implement. In all cases, the CSP object is used to access variables and constraints of the problem, via methods found in cspbase.py.
 

Brief implementation description: A Propagator Function takes as input a CSP object csp and (optionally) a variable newVar. The CSP object is used to access the variables and constraints of the problem (via methods found in cspbase.py). A propagator function returns a tuple of (bool,list) where bool is False if and only if a dead-end is found, and list is a list of (variable, value) tuples that have been pruned by the propagator. ord_mrv takes a CSP object as input, and returns a Variable object var. You must implement:
 

prop_FC (worth 25/100 marks): A propagator function that propagates according to the Forward Checking (FC) algorithm that check constraints that have exactly one uninstantiated variable in their scope, and prune appropriately. If newVar is None, forward check all constraints. Else, if newVar=var only check constraints containing newVar.
 

prop_GAC (worth 25/100 marks): A propagator function that propagates according to the Generalized Arc Consistency (GAC) algorithm, as covered in lecture. If newVar is None, run GAC on all constraints. Else, if newVar=var only check constraints containing newVar.
 

ord_mrv (worth 10/100 marks): A variable ordering heuristic that chooses the next variable to be assigned according to the Minimum Remaining Values (MRV) heuristic. ord mrv returns the variable with the most constrained current domain (i.e., the variable with the fewest legal values).

## Question 2: Futoshiki Models (worth 40/100 marks)
 

You will implement two different CSP encodings to solve the logic puzzle, Futoshiki. In one model you will use only binary not-equal constraints, while in the other model you will use n-ary all-different constraints in addition to binary not-equal constraints. These CSP models are briefly described below. The file futoshiki_csp.py provides the complete input/output specification for the two CSP encodings you are to implement.
 

The correct implementation of each encoding is worth 20/100 marks.
 

Brief implementation description: A Futoshiki Model takes as input a Futoshiki board, and returns a CSP object, consisting of a variable corresponding to each cell of the board. The variable domain of that cell is {1,...,n} if the board is unfilled at that position, and equal to i if the board has a fixed number i at that cell. All appropriate constraints will be added to the board as well. You must implement:
 

futoshiki_csp_model_1: A model built using only binary not equal constraints for the row and column constraints, and binary inequality constraints.
futoshiki_csp_model_2: A model built using n-ary all-different constraints for the row and column constraints, and binary inequality constraints.
 

Caveat: The Futoshiki CSP models you will construct can be space expensive, especially for constraints over many variables, (e.g., those contained in the second Futoshiki CSP model). HINT: Also be mindful of the time complexity of your methods for identifying satisfying tuples, especially when coding the second Futoshiki CSP model.
 

## What to Submit
You will be using MarkUs to submit your assignment. You will submit two files:

Your modified propagators.py
Your modified futoshiki_csp.py

# SAT-Based Juosan Solver

## Overview

This project is dedicated to solving Juosan puzzles&mdash;which have been proven to be NP-complete&mdash;using a SAT-based approach.
It works by encoding the rules of the Juosan puzzle input to propositional formulas and feeding the resulting formulas to a SAT solver. 
The SAT solver we use is MiniSAT, one of the field's most popular SAT solvers.
It can be shown that the encoding we implemented is polynomially proportional to the puzzle's size. Specifically, it is bounded by $O(m^2 n^2)$ where $m \times n$ is the puzzle size.

This repository is related to our works submitted to [ICoMPAC 2023](https://icompac.its.ac.id).
The proceedings, which include our paper, have been published by [Springer](https://link.springer.com/chapter/10.1007/978-981-97-2136-8_16).

Additionally, we have created a web application called [Juosan Interactive Playground](https://tsaqifammar.pythonanywhere.com).
This tool allows you to visualize, play, design puzzles, and explore our solver in an interactive environment.
The source code for this application can be found in the [juosan-interactive-playground](https://github.com/tsaqifammar/juosan-interactive-playground) repository.

For more information about the puzzle, see [https://www.nikoli.co.jp/en/puzzles/juosan](https://www.nikoli.co.jp/en/puzzles/juosan).

## Contents

This repository includes the following:

* **Juosan Solver**: The solver is implemented in C++ and use the solver MiniSAT. You can find the code in the `codes/sat-based-solver.cpp` file. Additionally, the compiled executable is also included.
* **Test Cases**: Seventy test cases of Juosan puzzles in plain text format sourced from [Janko](https://www.janko.at/Raetsel/Juosan/index.htm). You can find them in the `test_cases` directory.
* **Experimental Data**: Experimental data regarding the runtime of the solver to solve the aforementioned test cases. You can find the data in the `experimental_data/Juosan SAT Runtime Experiment.xlsx` file.

## How to use

Here are the steps to use the program that you need to follow:

1. Install MiniSAT and build the solver source code. We suggest reading [this article](https://medium.com/@timbersama2020/minisat-installation-guide-efb99a897138) for a guide to MiniSAT installation. You can skip this step if you just use the executable we provided.
2. Run the resulting executable file.
3. Input the Juosan puzzle according to the [Input/Output Format](#inputoutput-format) section.

## Input/Output Format

The Juosan puzzle can be inputted using the following format:

```
m n
r
N_1 N_2 ... N_r
R_{1,1} R_{1,2} ... R_{1,n}
R_{2,1} R_{2,2} ... R_{2,n}
...
R_{m,1} R_{m,2} ... R_{m,n}
```

where:

* `m` and `n` are integers representing the number of rows and columns in the puzzle.
* `r` is an integer representing the number of territories.
* `N_i` is the number occurring in territory $i$. If territory $i$ does not contain a number, then `N_i` $= -1$.
* `R_{i,j}` is an integer label of the territory containing cell $(i,j)$.

For example, the following input represents the Juosan puzzle depicted in the picture below:
```
6 6
14
3 1 3 4 3 3 -1 -1 -1 2 3 2 -1 2
1 4 4 4 4 4
1 5 6 8 10 10
1 5 6 8 11 13
2 5 6 8 11 14
2 5 7 7 11 14
3 3 3 9 12 12
```

<img src="https://github.com/tsaqifammar/juosan-sat/assets/54428874/4219a59b-1ae5-47ca-807f-f8df49999094" alt="example input" width="400">

Here is the output generated by the solver for the above input:
```
| | - - - -
| - | | - -
| - | - | |
- | | - | -
| - - | | -
- - - - | |
Time taken: 3.921 ms
```

Alternatively, the input can be fed from a text file.
For example, using `test_cases/6x6_1.in`&mdash;which follows the same format&mdash;like this:
```
[solver executable] < ../test_cases/6x6_1.in
```

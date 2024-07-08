%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%SAT solver with addition machinery to produce table in 
%FLOPS2010 paper.  Note this setup prevents backtracking
%for further solutions.
%
%Authors: Jacob Howe and Andy King
%Last modified: 5/4/11
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

:- use_module(library(terms)).
:- use_module(library(lists)).

:- module(sat_solver, [initialise/1, sat/2, search/4]).

initialise(_).  

search(Clauses, Vs, Sat, N):-
    bb_put(count, 0),
    sat(Clauses, Vs),!,
    bb_get(count, N),
    Sat = true.
search(_, _, false, N):-
    bb_get(count, N).

sat(Clauses, Vars) :- 
    problem_setup(Clauses), elim_var(Vars). 

elim_var([]). 
elim_var([Var | Vars]) :- 
    elim_var(Vars), 
    (
     (bb_get(count,N),(var(Var)->NewN is N+1; NewN = N),
       Var = true,
      bb_put(count,NewN)); 
     (bb_get(count,M),(var(Var)->NewM is M+1; NewM = M),
       Var = false,
      bb_put(count, NewM))
    ). 

problem_setup([]). 
problem_setup([Clause | Clauses]) :- 
    clause_setup(Clause), 
    problem_setup(Clauses). 

clause_setup([Pol-Var | Pairs]) :- set_watch(Pairs, Var, Pol). 

set_watch([], Var, Pol) :- Var = Pol.
set_watch([Pol2-Var2 | Pairs], Var1, Pol1):- 
    watch(Var1, Pol1, Var2, Pol2, Pairs). 

:- block watch(-, ?, -, ?, ?). 
watch(Var1, Pol1, Var2, Pol2, Pairs) :- 
    nonvar(Var1) -> 
      update_watch(Var1, Pol1, Var2, Pol2, Pairs);  
      update_watch(Var2, Pol2, Var1, Pol1, Pairs). 

update_watch(Var1, Pol1, Var2, Pol2, Pairs) :- 
    Var1 == Pol1 -> true; set_watch(Pairs, Var2, Pol2).


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%A sat solver, utilising delay declaration to implement
%watched literals
%
%Authors: Jacob Howe and Andy King
%Last modified: 5/4/11
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

:- module(sat_solver, [initialise/1, sat/2, search/4]).

initialise(_).  

search(Clauses, Vars, Sat, _) :-
    sat(Clauses, Vars),
    !,
    Sat = true.
search(_Clauses, _Vars, false, _).

sat(Clauses, Vars) :- 
    problem_setup(Clauses), elim_var(Vars). 

elim_var([]). 
elim_var([Var | Vars]) :- 
    elim_var(Vars), assign(Var).

assign(true).
assign(false).

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

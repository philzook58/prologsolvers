%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%A sat solver, utilising delay declaration to implement
%watched literals, plus state saving and restoration
%
%Authors: Jacob Howe and Andy King
%Last modified: 5/4/11
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

:- module(sat_solver, [initialise/1, sat/2, search/4]).
:- use_module(library(lists)).

initialise(State):-
    bb_put(history, State).  

search(Clauses, Vars, Sat, _) :-
    sat(Clauses, Vars),
    !,
    Sat = true.
search(_Clauses, _Vars, false, _).

sat(Clauses, Vars) :- 
    problem_setup(Clauses), elim_var(Vars), 
    reverse(Vars, Rev), bb_put(history, Rev).

elim_var([]).
elim_var([V|Vs]):-
    elim_var(Vs),
    assign(V).

assign(V):-
    bb_get(history, Hs),
    assign_true(Hs, V).
assign(V):-
    bb_get(history, Hs),
    assign_false(Hs, V).

assign_true([], true).
assign_true([true|Hs], Var):-
    (Var = true ->           
        bb_put(history, Hs)  
    ;
        bb_put(history, []),fail
    ).

assign_false([], false).
assign_false([false|Hs], Var):-
    (Var = false ->
        bb_put(history, Hs)
    ;
        bb_put(history, []), fail
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



%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%An SMT solver.  Requires a SAT solver and a theory.
%Coded for SICStus
%
%Authors: Jacob Howe and Andy King
%Last modified: 7/4/11
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

:- use_module(theory).
:- use_module(sat_solver_restore).
:- use_module(library(assoc)).

main :-
    Clauses = [[true-X], [true-Y, true-Z], [true-U, true-V], [false-W]],
    Vars = [X, Y, Z, U, V, W],
    empty_assoc(ConsMap0),
    put_assoc(X, ConsMap0, A < B, ConsMap1),
    put_assoc(Y, ConsMap1, A = 0, ConsMap2), 
    put_assoc(Z, ConsMap2, A = 1, ConsMap3), 
    put_assoc(U, ConsMap3, B = 0, ConsMap4), 
    put_assoc(V, ConsMap4, B = 1, ConsMap5), 
    put_assoc(W, ConsMap5, 1 =< A + B, ConsMap),
    smt(Clauses, Vars, ConsMap).

smt(Clauses, Vars, ConsMap):-
    initialise([]),
    smt_call(Clauses, Vars, ConsMap).

smt_call(Clauses, Vars, ConsMap) :-
    copy_term(Clauses-Vars, CopyClauses-CopyVars),
    sat(CopyClauses, CopyVars), !,
    zip(CopyVars, Vars, ZipVars),
    smt_proceed(ZipVars, Clauses, Vars, ConsMap).

smt_proceed(ZipVars, _Clauses, _Vars, ConsMap) :-
    satisfiable(ZipVars, [], ConsMap), !.
smt_proceed(ZipVars, Clauses, Vars, ConsMap) :-
    unsat_core(ZipVars, ConsMap, Min),
    new_clause(Min, Vars, NewClause),
    smt_call([NewClause | Clauses], Vars, ConsMap).

satisfiable([], Cons, _):- post_all(Cons).
satisfiable([Val-Var|Vals], Acc, ConsMap):-
    get_assoc(Var, ConsMap, Con),
    satisfiable(Vals, [Val-Con | Acc], ConsMap).

zip([], [], []).
zip([X|Xs], [Y|Ys], [X-Y|Zs]):- zip(Xs, Ys, Zs).

new_clause([], _, []).
new_clause([Val | Vals], Vars, Rest) :-
    new_clause(Val, Vals, Vars, Rest).

new_clause(true, Vals, [Var | Vars], [false-Var | Rest]) :-
    new_clause(Vals, Vars, Rest).
new_clause(false, Vals, [Var | Vars], [true-Var | Rest]) :-
    new_clause(Vals, Vars, Rest).
new_clause(na, Vals, [_ | Vars], Rest) :-
    new_clause(Vals, Vars, Rest).

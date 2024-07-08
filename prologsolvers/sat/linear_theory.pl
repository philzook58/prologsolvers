%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%Decision procedure for conjunctions of literals in the
%theory of linear real arithmetic for an SMT solver.
%Coded for SICStus, requires CLP(R).
%
%Authors: Jacob Howe and Andy King
%Last modified: 10/9/10
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

:- module(theory, [post_all/1, unsat_core/3]).
:- use_module(library(clpr)).
:- use_module(library(assoc)).

post_all([]).
post_all([Val-C|Cs]):-
    post_con(Val, C),
    post_all(Cs).

post_con(true, Con) :- post_true(Con).
post_con(false, Con) :- post_false(Con).

post_true(triv).
post_true(X=<Y) :- {X=<Y}.
post_true(X<Y) :- {X<Y}.
post_true(X=Y) :- {X=Y}.

post_false(triv).
post_false(X=<Y) :- {X>Y}.
post_false(X<Y) :- {X>=Y}.
post_false(X=Y) :- {X=\=Y}.

unsat_core(VarMap, ConsMap, Min) :-
    assoc_to_vals(VarMap, ConsMap, [], Cons),
    remove_redundant(Cons, [], [], Min).

assoc_to_vals([], _, Cons, Cons).
assoc_to_vals([Val-Var|VarMap], ConsMap, Acc, Vs) :-
    get_assoc(Var, ConsMap, Con),
    assoc_to_vals(VarMap, ConsMap, [Val-Con|Acc], Vs).

check_redundant(Val-Con, Cons, TestedCons, Core, Min) :-
    append(Cons, TestedCons, AllCons),
    copy_term(AllCons, CopyCons),
    post_all(CopyCons),!,
    remove_redundant(Cons, [Val-Con | TestedCons], [Val | Core], Min).
check_redundant(_, Cons, Tested, Core, Min) :-
    remove_redundant(Cons, Tested, [na | Core],  Min).

remove_redundant([], _, Min, Min).
remove_redundant([C|Cs],Tested, Core, Min) :-
    check_redundant(C, Cs, Tested, Core, Min). 

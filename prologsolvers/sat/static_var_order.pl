%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%Static variable ordering for a SAT solver
%
%Authors: Jacob Howe and Andy King
%Last modified: 5/4/11
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

:- module(static_var_order, [order_variables/3]).
:- use_module(library(lists)).

order_variables(Clauses, Vars, Ordered_Vars):-
	initial_counts(Vars, VarsZero),
	run_over_clauses(Clauses, VarsZero, VarsCounts),
	quicksort(VarsCounts, OrderedCounts),
	strip_counts(OrderedCounts, Ordered_Vars).

run_over_clauses([], Vs, Vs).
run_over_clauses([C | Cs], Vs, VsCounts):-
	run_over_clause(C, Cs, Vs, VsCounts).

run_over_clause([], Cs, Vs, VsCounts):-
	run_over_clauses(Cs, Vs, VsCounts).
run_over_clause([_-L | Ls], Cs, Vs, VsCounts):-
	inc_counts(Vs, L, NewVs),
	run_over_clause(Ls, Cs, NewVs, VsCounts).

inc_counts([], _, []).
inc_counts([Count-V | Vs], L, NewVs):-
	V \== L, !,
	inc_counts(Vs, L, VsInc),
	NewVs = [Count-V | VsInc].
inc_counts([Count-V | Vs], _, NewVs):-
	NewCount is Count+1,
	NewVs = [NewCount-V | Vs].
	
initial_counts([], []).
initial_counts([V | Vs], [0-V | VCs]):-
	initial_counts(Vs, VCs).


strip_counts([], []).
strip_counts([_-X | CTs], [X | Ts]):-
	strip_counts(CTs, Ts).

quicksort([],[]).
quicksort([X|Xs],Ys) :-
        partition(Xs,X,LessOrEqual,Greater),
        quicksort(LessOrEqual,LEs),
        quicksort(Greater,Gs),
        append(LEs,[X|Gs],Ys).

partition([],_Y,[],[]).
partition([Count1-X|Xs],Count2-Y,[Count1-X|LessOrEqual],Greater) :-
        Count1 < Count2,
        partition(Xs,Count2-Y,LessOrEqual,Greater).
partition([Count1-X|Xs],Count2-Y,LessOrEqual,[Count1-X|Greater]) :-
        Count1 >= Count2,
        partition(Xs,Count2-Y,LessOrEqual,Greater).

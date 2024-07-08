%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%A sat solver that learns clauses
%
%Authors: Jacob Howe and Andy King
%Last modified: 6/4/10
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

:- module(sat_solver, [initialise/1, sat/2, search/4]).

initialise(_).

search(Clauses, Vars, Sat, _) :-
    sat(Clauses, Vars),
    !,
    Sat = true.
search(_Clauses, _Vars, false, _).

sat(Clauses, Vars) :-
    bb_put(learn, []),
    length(Vars, N),
    special_reverse(Vars, N, [], RevVars),
    problem_setup(Clauses), !,
    solve(RevVars).

special_reverse([], _, Vs, Vs).
special_reverse([V|Vs], N, R, Rev):-
    NewN is N-1,
    special_reverse(Vs, NewN, [N-V | R], Rev).

solve(Vars):-
    elim_var(Vars), !.
solve(Vars):-
    learning(Vars),!,
    solve(Vars).

learning(Vars):-
    bb_get(learn, L),
    buildclause(L, Vars, Clause), !,
    problem_setup([Clause]).

buildclause([], _, []).
buildclause([N|History], [N-Var|Vars], [false-Var|Clause]):-!,
    buildclause(History, Vars, Clause).
buildclause(History, [_|Vars], Clause):-
    buildclause(History, Vars, Clause).

negate(true, false).
negate(false, true).

elim_var([]).
elim_var([N-Var|Vars]):-
    var(Var),!,
    Var = true-[N],
    elim_var(Vars).
elim_var([_|Vars]):-
    elim_var(Vars).

problem_setup([]).
problem_setup([Clause | Clauses]) :-
    clause_setup(Clause),
    problem_setup(Clauses).

clause_setup([Pol-Var | Pairs]) :- set_watch(Pairs, Var, Pol, []).

set_watch([], Var, Pol, Assigns):-
    var(Var), !,
    Var = Pol-Assigns.
set_watch([], Var, Pol, Assigns):-!,
    Var = Val-Inf,
    (Val == Pol -> true; (merge(Inf, Assigns, NewAss), bb_put(learn, NewAss), fail)).
set_watch([Pol2-Var2 | Pairs], Var1, Pol1, Assigns):-
    watch(Var1, Pol1, Var2, Pol2, Pairs, Assigns).

:- block watch(-, ?, -, ?, ?, ?).
watch(Var1, Pol1, Var2, Pol2, Pairs, Assigns) :-
    nonvar(Var1) ->
        update_watch(Var1, Pol1, Var2, Pol2, Pairs, Assigns);
        update_watch(Var2, Pol2, Var1, Pol1, Pairs, Assigns).

update_watch(Var1-Inf, Pol1, Var2, Pol2, Pairs, Assigns) :-
    Var1 == Pol1 -> true;
    (
    merge(Inf, Assigns, NewAss),
    set_watch(Pairs, Var2, Pol2, NewAss)).

merge([], Ys, Ys):-!.
merge(Xs, [], Xs):-!.
merge([X|Xs], [Y|Ys], Zs):-
    X < Y, !,
    Zs = [X|Rest],
    merge(Xs, [Y|Ys], Rest).
merge([X|Xs], [Y|Ys], Zs):-
    X > Y, !,
    Zs = [Y|Rest],
    merge([X|Xs], Ys, Rest).
merge([X|Xs], [Y|Ys], Zs):-
    X == Y,
    Zs = [X|Rest],
    merge(Xs, Ys, Rest).

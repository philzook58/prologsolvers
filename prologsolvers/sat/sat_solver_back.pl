%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%A sat solver, utilising delay declaration to implement
%watched literals, with some backjumping
%
%Authors: Jacob Howe and Andy King
%Last modified: 5/4/11
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

:- module(sat_solver, [initialise/1, sat/2, search/4]).

initialise(_).

search(Clauses, Vars, true, N):-
    bb_put(count, 0),
    sat(Clauses, Vars), !, 
    bb_get(count, N).
%search(_,_,false, _N).
search(_,_,false, N) :-
    bb_get(count, N).

sat(Clauses, Vars) :- 
    problem_setup(Clauses), elim_var(Vars, 1). 

elim_var([], N):-clear(N). 
elim_var([Var | Vars], N) :- 
    NewN is N+1,
    elim_var(Vars, NewN), assign(Var, NewN).

clear(0):-!.
clear(N):-
    (bb_delete(N,_);true),!,
    Dec is N-1,
    clear(Dec).

assign(Var, N):-
    nonvar(Var), !,
    bb_put(N, []).
assign(Var, N):-
    Var = true-[N],
    bb_get(count, C), NewC is C+1, bb_put(count, NewC).
assign(Var, N):-
    bb_get(N, Infl),
    continue(Infl,N),
    Var = false-[N],
    bb_get(count, C), NewC is C+1, bb_put(count, NewC). 

continue([N | _], N):-!.
continue(Ns, M):-
    NewM is M+1,
    update_aux(NewM, Ns),
    bb_delete(M, _), 
    fail.

problem_setup([]). 
problem_setup([Clause | Clauses]) :- 
    clause_setup(Clause), 
    problem_setup(Clauses). 

clause_setup([Pol-Var | Pairs]) :- set_watch(Pairs, Var, Pol, []). 

set_watch([], Var, Pol, _Infl) :- 
    nonvar(Var), 
    Var = V-_, V = Pol, !.
set_watch([], Var, _Pol, Infl) :- 
    nonvar(Var), 
    Var = _V-InflV,
    merge(InflV, Infl, NewInfl), 
    update(NewInfl),
    fail.
set_watch([], Var, Pol, Infl) :- 
    Var = Pol-Infl. 
set_watch([Pol2-Var2 | Pairs], Var1, Pol1, Infl):- 
    watch(Var1, Pol1, Var2, Pol2, Pairs, Infl). 

update([N | Is]):-
    update_aux(N, [N | Is]).

update_aux(N, Is1):-
    bb_get(N, Is2), !,
    merge(Is1, Is2, Is),
    decapitate_if_needed(Is, N, Dec),
    NewN is N+1,
    bb_delete(N, _),
    update_aux(NewN, Dec).
update_aux(N, Is):-
    bb_put(N, Is).

decapitate_if_needed([N | Dec], N, Dec):-!.
decapitate_if_needed(Dec, _, Dec).

:- block watch(-, ?, -, ?, ?, ?). 
watch(Var1, Pol1, Var2, Pol2, Pairs, Infl) :- 
    nonvar(Var1) -> 
        update_watch(Var1, Pol1, Var2, Pol2, Pairs, Infl); 
        update_watch(Var2, Pol2, Var1, Pol1, Pairs, Infl). 

update_watch(Var1, Pol1, Var2, Pol2, Pairs, Infl) :- 
    Var1 = Var-InflV,
    (Var == Pol1 -> true; 
        (merge(InflV, Infl, NewInfl), set_watch(Pairs, Var2, Pol2, NewInfl))).

merge([], Ys, Ys):-!.
merge(Xs, [], Xs):-!.
merge([X|Xs], [Y|Ys], Zs):-
    X < Y, !,
    Zs = [X|Rest],
    merge(Xs, [Y | Ys], Rest).
merge([X|Xs], [Y|Ys], Zs):-
    X > Y, !,
    Zs = [Y|Rest],
    merge([X | Xs], Ys, Rest).
merge([X|Xs], [Y|Ys], Zs):-
    X == Y,
    Zs = [X|Rest],
    merge(Xs, Ys, Rest).

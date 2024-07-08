
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%A normalisation procedure
%
%Authors: Jacob Howe and Andy King
%Last modified: 10/9/10
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%main(CNF, Map) :- 
%	cnf(and(or(and(a == f(d), c == h(f(d))),
%	           and([a == g(d, e), c == h(g(e, d)), d == e])), c =\= h(a)), CNF, Map),
%	write_term(CNF-Map, [max_depth(0)]).

main(CNF, Map) :- 
	cnf(and(or(and(a == b, b == g(c)), and(a == g(b), b == c)), a =\= g(c)), CNF, Map),
	write_term(CNF-Map, [max_depth(0)]).

%main(CNF, Map) :-
%	cnf(imply(and([X < Y, or(X=0, Y=0), or(Y=0, Y=1)]), X+Y>=1), CNF, Map),
%	write_term(CNF-Map, [max_depth(0)]).

cnf(A, CNFout, Mapout) :-
	cnf(A, W, [[true-W]], CNFout, [], Mapin, [], Fresh),
	sort(Fresh, OrderedFresh),
	equate_fresh_vars(OrderedFresh),
	equate_witness_vars(Mapin, Mapout).

equate_fresh_vars([]).
equate_fresh_vars([Term1 == Var1 | Eqns]) :- equate_fresh_vars(Eqns, Term1, Var1) .

equate_fresh_vars([], _Term1, _Var1) .
equate_fresh_vars([Term2 == Var2 | Eqns], Term1, Var1) :-
	(Term1 == Term2 ->
		Var1 = Var2
	;
		true
	),
	equate_fresh_vars(Eqns, Term2, Var2).

equate_witness_vars(Mapin, Mapout) :-
	invert(Mapin, InvertedMapin),
	sort(InvertedMapin, OrderedMapin),
	equate_witness_vars_aux(OrderedMapin, Mapout).

invert([], []).
invert([Var-Con|Map], [Con-Var | InvertedMap]) :- invert(Map, InvertedMap).
	
equate_witness_vars_aux([], []).
equate_witness_vars_aux([Con-Var | InvertedMap], Map) :-
	equate_witness_vars_aux(InvertedMap, Con, Var, [], Map).

equate_witness_vars_aux([], Con, Var, AccMap, Map) :-
	Map = [Var-Con | AccMap].
equate_witness_vars_aux([Con2-Var2 | InvertedMap], Con1, Var1, AccMap, Map) :-
	(Con1 \== triv, Con2 \== triv, Con1 == Con2 ->
		Var1 = Var2,
		equate_witness_vars_aux(InvertedMap, Con2, Var2, AccMap, Map)
	;
		equate_witness_vars_aux(InvertedMap, Con2, Var2, [Var1-Con1 | AccMap], Map)
	).

cnf(A, W, CNFin, CNFout, Mapin, Mapout, Fresh, Fresh) :-
	simple(A), 
	!,
	A = W,
	CNFout = CNFin,
	Mapout = [A-triv | Mapin].
%cnf(X = Y, W, CNFin, CNFout, Mapin, Mapout, Freshin, Freshout) :-
%	cnf(and(Y =< X, X =< Y), W, CNFin, CNFout, Mapin, Mapout, Freshin, Freshout).
cnf(X = Y, W, CNFin, CNFout, Mapin, Mapout, Fresh, Fresh) :-
	CNFout = CNFin,
	Mapout = [W-(X = Y) | Mapin].
cnf(X < Y, W, CNFin, CNFout, Mapin, Mapout, Freshin, Freshout) :-
	cnf(not(Y =< X), W, CNFin, CNFout, Mapin, Mapout, Freshin, Freshout).
cnf(X > Y, W, CNFin, CNFout, Mapin, Mapout, Freshin, Freshout) :-
	cnf(Y < X, W, CNFin, CNFout, Mapin, Mapout, Freshin, Freshout).
cnf(X >= Y, W, CNFin, CNFout, Mapin, Mapout, Freshin, Freshout) :-
	cnf(Y =< X, W, CNFin, CNFout, Mapin, Mapout, Freshin, Freshout).
cnf(X =< Y, W, CNFin, CNFout, Mapin, Mapout, Fresh, Fresh) :-
	CNFout = CNFin,
	Mapout = [W-(X =< Y) | Mapin].
cnf(X == Y, W, CNFin, CNFout, Mapin, Mapout, Freshin, Freshout) :-
	curry_eqns([X == Y], CurriedEqns),
	flatten_eqns(CurriedEqns, [], SimpleEqns, Freshin, Freshout),
	cnf_simple_eqns(SimpleEqns, [], W, CNFin, CNFout, Mapin, Mapout).
cnf(X =\= Y, W, CNFin, CNFout, Mapin, Mapout, Freshin, Freshout) :-
	cnf(not(X == Y), W, CNFin, CNFout, Mapin, Mapout, Freshin, Freshout).
cnf(not(A), W, CNFin, CNFout, Mapin, Mapout, Freshin, Freshout) :-
	cnf(A, W1, [[true-W, true-W1], [false-W, false-W1] | CNFin], CNFout, [W-triv | Mapin], Mapout, Freshin, Freshout).
cnf(or(A, B), W, CNFin, CNFout, Mapin, Mapout, Freshin, Freshout) :-
	cnf(A, WA, [[false-WA, true-W], [false-WB, true-W], [true-WA, true-WB, false-W] | CNFin], CNFmid, [W-triv | Mapin], Mapmid, Freshin, Freshmid),
	cnf(B, WB, CNFmid, CNFout, Mapmid, Mapout, Freshmid, Freshout).
cnf(imply(A, B), W, CNFin, CNFout, Mapin, Mapout, Freshin, Freshout) :-
	cnf(A, WA, [[true-WA, true-W], [false-WB, true-W], [false-WA, true-WB, false-W] | CNFin], CNFmid, [W-triv | Mapin], Mapmid, Freshin, Freshmid),
	cnf(B, WB, CNFmid, CNFout, Mapmid, Mapout, Freshmid, Freshout).
cnf(and(A, B), W, CNFin, CNFout, Mapin, Mapout, Freshin, Freshout) :-
	cnf(A, WA, [[true-WA, false-W], [true-WB, false-W], [false-WA, false-WB, true-W] | CNFin], CNFmid, [W-triv | Mapin], Mapmid, Freshin, Freshmid),
	cnf(B, WB, CNFmid, CNFout, Mapmid, Mapout, Freshmid, Freshout).
cnf(and(As), W, CNFin, CNFout, Mapin, Mapout, Freshin, Freshout) :-
	cnf_and(As, [true-W], W, CNFin, CNFout, Mapin, Mapout, Freshin, Freshout).

cnf_and([], Clause, W, CNFin, CNFout, Mapin, Mapout, Freshin, Freshout) :-
	CNFout = [Clause | CNFin],
	Mapout = [W-triv | Mapin],
	Freshout = Freshin.
cnf_and([A | As], Clause, W, CNFin, CNFout, Mapin, Mapout, Freshin, Freshout) :-
	cnf(A, WA, CNFin, CNFmid, Mapin, Mapmid, Freshin, Freshmid),
	cnf_and(As, [false-WA | Clause], W, [[true-WA, false-W] | CNFmid], CNFout, Mapmid, Mapout, Freshmid, Freshout).

cnf_simple_eqns([], Ws, W, CNFin, CNFout, Mapin, Mapout) :-
	CNFout = [[true-W | Ws] | CNFin],
	Mapout = [W-triv | Mapin].
cnf_simple_eqns([Eqn | Eqns], Ws, W, CNFin, CNFout, Mapin, Mapout) :-
	cnf_simple_eqns(Eqns, [false-WEqn | Ws], W, [[true-WEqn, false-W] | CNFin], CNFout, [WEqn-Eqn | Mapin], Mapout).

flatten_eqns([], FlatEqns, FlatEqns, Fresh, Fresh).
flatten_eqns([A == B | Eqns], AccEqns, FlatEqns, Freshin, Freshout) :-
	simple(A), simple(B), !, 
	flatten_eqns(Eqns, [A == B | AccEqns], FlatEqns, Freshin, Freshout).
flatten_eqns([A == B | Eqns], AccEqns, FlatEqns, Freshin, Freshout) :- % nothing can be inferred
	compound(A), compound(B), !,
	flatten_eqns(Eqns, AccEqns, FlatEqns, Freshin, Freshout).
flatten_eqns([A == B | Eqns], AccEqns, FlatEqns, Freshin, Freshout) :-
	simple(A), compound(B), !,
	flatten_eqns([B == A | Eqns], AccEqns, FlatEqns, Freshin, Freshout).
flatten_eqns([f(A1, A2) == B | Eqns], AccEqns, FlatEqns, Freshin, Freshout) :-
	simple(A1), simple(A2), simple(B), !,
	flatten_eqns(Eqns, [f(A1, A2) == B | AccEqns], FlatEqns, Freshin, Freshout).
flatten_eqns([f(A1, A2) == B | Eqns], AccEqns, FlatEqns, Freshin, Freshout) :-
	compound(A1), simple(B), !,
	flatten_eqns([f(NewA1, A2) == B, A1 == NewA1 | Eqns], AccEqns, FlatEqns, [A1 == NewA1 | Freshin], Freshout).
flatten_eqns([f(A1, A2) == B | Eqns], AccEqns, FlatEqns, Freshin, Freshout) :-
	compound(A2), simple(B),
	flatten_eqns([f(A1, NewA2) == B, A2 == NewA2 | Eqns], AccEqns, FlatEqns, [A2 == NewA2 | Freshin], Freshout).

curry_eqns([], []).
curry_eqns([A == B | Eqns], [CurriedA == CurriedB | CurriedEqns]) :-
	curry_term(A, CurriedA),
	curry_term(B, CurriedB),
	curry_eqns(Eqns, CurriedEqns).

curry_term(Term, CurriedTerm) :-
	simple(Term) ->
		CurriedTerm = Term
	;
		Term =.. [Functor | Args],
		curry_terms(Args, CurriedArgs),
		curry_args(CurriedArgs, Functor, CurriedTerm)
	.

curry_args([], Term, Term).
curry_args([Arg | Args], Term, CurriedTerm) :-
	curry_args(Args, f(Term, Arg), CurriedTerm).

curry_terms([], []).
curry_terms([Term | Terms], [CurriedTerm | CurriedTerms]) :-
	curry_term(Term, CurriedTerm),
	curry_terms(Terms, CurriedTerms).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%Decision procedure for uninterpreted functors
%
%Authors: Jacob Howe and Andy King
%Last modified: 10/9/10
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

:- module(theory, [post_all/1, unsat_core/3]).
:- use_module(library(avl)).
:- use_module(library(assoc)).

main :- post_all([true-(b==c),false-(f(g,c)==a)]).

post_all(Eqns) :- post_all(Eqns, [], []).

post_all([], Eqs, DisEqs) :-
	my_empty_assoc(RepMap1),
	my_empty_assoc(ClassMap1),
	my_empty_assoc(LookMap1),
	my_empty_assoc(UseMap1),
	setup_maps(Eqs, RepMap1, RepMap2, ClassMap1, ClassMap2, UseMap1, UseMap2),
	setup_maps(DisEqs, RepMap2, RepMap3, ClassMap2, ClassMap3, UseMap2, UseMap3),
	merge(Eqs, RepMap3, RepMap4, ClassMap3, _ClassMap4, LookMap1, LookMap3, UseMap3, _UseMap4),
	check(DisEqs, RepMap4, LookMap3).
post_all([_Bool-triv | Eqns], Eqs, DisEqs) :-
	!,
	post_all(Eqns, Eqs, DisEqs).
post_all([Bool-Eqn | Eqns], Eqs, DisEqs) :-
	(Bool == true ->
		post_all(Eqns, [Eqn | Eqs], DisEqs)
	;
		post_all(Eqns, Eqs, [Eqn | DisEqs])
	).

setup_maps([], RepMap, RepMap, ClassMap, ClassMap, UseMap, UseMap).
setup_maps([Term | Terms], RepMap1, RepMap3, ClassMap1, ClassMap3, UseMap1, UseMap3) :-
	simple(Term), !,
	(my_get_assoc(Term, RepMap1, _Rep) ->
		RepMap2 = RepMap1,
		ClassMap2 = ClassMap1,
		UseMap2 = UseMap1
	;
		my_put_assoc(Term, RepMap1, Term, RepMap2),
		my_put_assoc(Term, ClassMap1, [Term], ClassMap2),
		my_put_assoc(Term, UseMap1, [], UseMap2)
	),
	setup_maps(Terms, RepMap2, RepMap3, ClassMap2, ClassMap3, UseMap2, UseMap3).
setup_maps([Term1 == Term2 | Eqs], RepMap1, RepMap3, ClassMap1, ClassMap2, UseMap1, UseMap2) :-
	!,
	setup_maps([Term1, Term2 | Eqs], RepMap1, RepMap3, ClassMap1, ClassMap2, UseMap1, UseMap2).
setup_maps([Term1 =\= Term2 | Eqs], RepMap1, RepMap3, ClassMap1, ClassMap2, UseMap1, UseMap2) :-
	!,
	setup_maps([Term1, Term2 | Eqs], RepMap1, RepMap3, ClassMap1, ClassMap2, UseMap1, UseMap2).
setup_maps([f(Term1, Term2) | Eqs], RepMap1, RepMap2, ClassMap1, ClassMap2, UseMap1, UseMap2) :-
	setup_maps([Term1, Term2 | Eqs], RepMap1, RepMap2, ClassMap1, ClassMap2, UseMap1, UseMap2).

monitor(Eqs, RepMap, _ClassMap, LookMap, UseMap) :-
	assoc_to_list(RepMap, RepList),
	assoc_to_list(LookMap, LookList),
	assoc_to_list(UseMap, UseList),
	format("~nEqs, RepMap, LookMap, UseMap = ~w, ~w, ~w, ~w", [Eqs, RepList, LookList, UseList]).

merge([], RepMap, RepMap, ClassMap, ClassMap, LookMap, LookMap, UseMap, UseMap) :-
%	monitor([], RepMap, ClassMap, LookMap, UseMap),
	true.
merge([A == B | Eqs], RepMap1, RepMap3, ClassMap1, ClassMap3, LookMap1, LookMap3, UseMap1, UseMap3) :-
%	monitor([A == B | Eqs], RepMap1, ClassMap1, LookMap1, UseMap1),
	simple(A), simple(B), !,
	pending([A == B], RepMap1, RepMap2, ClassMap1, ClassMap2, LookMap1, LookMap2, UseMap1, UseMap2),
	merge(Eqs, RepMap2, RepMap3, ClassMap2, ClassMap3, LookMap2, LookMap3, UseMap2, UseMap3).
merge([f(A1, A2) == A | Eqs], RepMap1, RepMap3, ClassMap1, ClassMap3, LookMap1, LookMap3, UseMap1, UseMap4) :-
	my_get_assoc(A1, RepMap1, RepA1),
	my_get_assoc(A2, RepMap1, RepA2),
	(my_get_assoc(RepA1-RepA2, LookMap1, f(D1, D2) == D) ->
		pending([(f(RepA1, RepA2) == A, f(D1, D2) == D)], RepMap1, RepMap2, ClassMap1, ClassMap2, LookMap1, LookMap2, UseMap1, UseMap3)
	;
		my_put_assoc(RepA1-RepA2, LookMap1, f(RepA1, RepA2) == A, LookMap2),
		my_get_assoc(RepA1, UseMap1, Use1),
		my_get_assoc(RepA2, UseMap1, Use2),
		my_put_assoc(RepA1, UseMap1, [f(RepA1, RepA2) == A | Use1], UseMap2),
		my_put_assoc(RepA2, UseMap2, [f(RepA1, RepA2) == A | Use2], UseMap3),
		RepMap2 = RepMap1,
		ClassMap2 = ClassMap1
	),
	merge(Eqs, RepMap2, RepMap3, ClassMap2, ClassMap3, LookMap2, LookMap3, UseMap3, UseMap4).

pending([], RepMap, RepMap, ClassMap, ClassMap, LookMap, LookMap, UseMap, UseMap).
pending([Eq | Pending1], RepMap1, RepMap3, ClassMap1, ClassMap4, LookMap1, LookMap3, UseMap1, UseMap4) :-
	(Eq = (A == B) ->
		true
	;
		Eq = (f(_, _) == A, f(_, _) == B)
	),
	my_get_assoc(A, RepMap1, RepA),
	my_get_assoc(B, RepMap1, RepB),
	(RepA == RepB ->
		Pending2 = Pending1,
		RepMap2 = RepMap1,
		ClassMap3 = ClassMap1,
		LookMap2 = LookMap1,
		UseMap3 = UseMap1
	;
		my_del_assoc(RepA, ClassMap1, Terms1, ClassMap2),
		my_get_assoc(RepB, ClassMap2, Terms2),
		append(Terms1, Terms2, Terms),
		my_put_assoc(RepB, ClassMap2, Terms, ClassMap3),
		update_repmap(Terms1, RepB, RepMap1, RepMap2),
		my_del_assoc(RepA, UseMap1, Eqs, UseMap2), 
		update_lookmap(Eqs, RepMap2, LookMap1, LookMap2, UseMap2, UseMap3, Pending1, Pending2)
	),
	pending(Pending2, RepMap2, RepMap3, ClassMap3, ClassMap4, LookMap2, LookMap3, UseMap3, UseMap4).

update_repmap([], _Rep, RepMap, RepMap).
update_repmap([Term | Terms], Rep, RepMap1, RepMap3) :-
	my_put_assoc(Term, RepMap1, Rep, RepMap2),
	update_repmap(Terms, Rep, RepMap2, RepMap3).

update_lookmap([], _RepMap, LookMap, LookMap, UseMap, UseMap, Pending, Pending).
update_lookmap([f(C1, C2) == C | Eqs], RepMap, LookMap1, LookMap3, UseMap1, UseMap4, Pending1, Pending2) :-
	my_get_assoc(C1, RepMap, RepC1),
	my_get_assoc(C2, RepMap, RepC2),
	(my_get_assoc(RepC1-RepC2, LookMap1, f(D1, D2) == D) ->
		update_lookmap(Eqs, RepMap, LookMap1, LookMap2, UseMap1, UseMap4, [(f(RepC1, RepC2) == C, f(D1, D2) == D) | Pending1], Pending2) 
	;
		my_put_assoc(RepC1-RepC2, LookMap1, f(RepC1, RepC2) == C, LookMap2),
		(my_get_assoc(RepC1, UseMap1, EqsC1) ->
			filter_usemap(EqsC1, RepMap, [f(RepC1, RepC2) == C], FilterEqsC1)
		;
			FilterEqsC1 = [f(RepC1, RepC2) == C]
		),
		my_put_assoc(RepC1, UseMap1, FilterEqsC1, UseMap2),
		(my_get_assoc(RepC2, UseMap2, EqsC2) ->
			filter_usemap(EqsC2, RepMap, [f(RepC1, RepC2) == C], FilterEqsC2)
		;
			FilterEqsC2 = [f(RepC1, RepC2) == C]
		),
		my_put_assoc(RepC2, UseMap2, FilterEqsC2, UseMap3),
		update_lookmap(Eqs, RepMap, LookMap2, LookMap3, UseMap3, UseMap4, Pending1, Pending2)
	).

filter_usemap([], _, AccEqs, FilterEqs) :-
	sort(AccEqs, FilterEqs).
filter_usemap([f(A1, A2) == A | Eqs], RepMap, AccEqs, FilterEqs) :-
	my_get_assoc(A1, RepMap, RepA1),
	my_get_assoc(A2, RepMap, RepA2),
	filter_usemap(Eqs, RepMap, [f(RepA1, RepA2) == A | AccEqs], FilterEqs).

% my_empty_assoc(Assoc) :-                empty_avl(Assoc).
% my_get_assoc(Key, Map, Value) :-        avl_fetch(Key, Map, Value).
% my_put_assoc(Key, Map1, Value, Map2) :- avl_store(Key, Map1, Value, Map2).
% my_del_assoc(Key, Map1, Value, Map2) :- avl_delete(Key, Map1, Value, Map2).  % fixed in SICStus 4.1.2

my_empty_assoc(Assoc) :-                empty_assoc(Assoc).
my_get_assoc(Key, Map, Value) :-        get_assoc(Key, Map, Value).
my_put_assoc(Key, Map1, Value, Map2) :- put_assoc(Key, Map1, Value, Map2).
my_del_assoc(Key, Map1, Value, Map2) :- get_assoc(Key, Map1, Value), put_assoc(Key, Map1, bot, Map2).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

check([], _RepMap, _LookMap).
check([A == B | DisEqs], RepMap, LookMap) :-
	simple(A), !,
	get_assoc(A, RepMap, RepA),
	get_assoc(B, RepMap, RepB),
	RepA \== RepB,
	check(DisEqs, RepMap, LookMap).
check([f(A1, A2) == A | DisEqs], RepMap, LookMap) :-
	get_assoc(A1, RepMap, RepA1),
	get_assoc(A2, RepMap, RepA2),
	(get_assoc(RepA1-RepA2, LookMap, (f(_, _) == B)) ->
		get_assoc(A, RepMap, RepA),
		get_assoc(B, RepMap, RepB),
		RepA \== RepB
	;
		true
	),
	check(DisEqs, RepMap, LookMap).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

unsat_core(VarMap, ConstraintMap, Min) :-
    assoc_to_vals(VarMap, ConstraintMap, [], Cons),
    remove_red_aux(Cons, [], [], Min).

assoc_to_vals([], _, Cons, Cons).
assoc_to_vals([Val-Var|VarMap], ConstraintMap, Acc, Vs) :-
    my_get_assoc(Var, ConstraintMap, Con),
    assoc_to_vals(VarMap, ConstraintMap, [Val-Con|Acc], Vs).

remove_red(Val-C, Cs, Tested, Thing, Min) :-
    copy_term(Cs-Tested, CCs-CTested),
    append(CTested, CCs, Combo),
    post_all(Combo), !,
    remove_red_aux(Cs, [Val-C | Tested], [Val | Thing], Min).
remove_red(_, Cs, Tested, Thing, Min) :-
    remove_red_aux(Cs, Tested, [na | Thing],  Min).

remove_red_aux([], _Tested, Min, Min).
remove_red_aux([C|Cs],Tested, Thing, Min) :-
    remove_red(C, Cs, Tested, Thing, Min). 

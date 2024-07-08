% setlog_tc-2.3h4


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
% {log} type-checker
% for version 4.9.8-7g or newer
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
%           by Maximiliano Cristia' and  Gianfranco Rossi
%                          January 2021
%
%                     Revised February 2024
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% interface
%   typecheck(F,VN)
%   declare_type(Tid,Tdef)
%   + user commands

:- dynamic(type/2).
:- dynamic(cons_type/2).
:- dynamic(enum/1).
:- dynamic(p_type/1).
:- dynamic(pp_type/1).
:- dynamic(pp_type/2).
:- dynamic(typedec/2).
:- dynamic(fintype/1).
:- dynamic(basic/1).

% typecheck(F,VN)
% F is a formula
% or
%   head :- body
% or
%   :- body
% where head is a functor followed by its arguments and
% body is a formula
% VN is a list as returned by read_term
% int and str are built-in types 
%   (i.e. the types of the integer numbers and strings)
%
typecheck(F,VN) :-
  retractall(type(_,_)),
  typecheck_clause(F,VN),!,
     b_setval(vn,VN).     % VN is saved for check_finite_types
typecheck(_,_) :-
    throw(setlog_excpt('type error')).


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
% typecheck clauses
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% typecheck_clause(C,VN)
%   C is the clause to typecheck
%   VN are the variable names
%
% In a clause head (i.e. H) all arguments are assumed to be
% variables. Then definitions such as:
%
% p(1,X) :- X = 5.
%
% aren't allowed because the first argument of p must be a variable
%
typecheck_clause((H :- true),VN) :-
  H =.. [F|P], F == dec_p_type,!,
  (P = [_] ->
     declare_p_type(H,VN)
  ;
     print_type_error_clause2(H,VN)
  ).
typecheck_clause((H :- true),VN) :-
  H =.. [F|P], F == dec_pp_type,!,
  (P = [_] ->
     declare_pp_type(H,VN)
  ;
     print_type_error_clause2(H,VN)
  ).
typecheck_clause((H :- true),VN) :-
  H =.. [F|P], F == def_type,!,
  (P = [I,T], declare_type(I,T) ->
      true
  ;
      print_type_error_dec_type(H,VN)
  ).
typecheck_clause((_ :- true),_) :- !.              % facts aren't typed
typecheck_clause((:- B),VN) :- !,
  typecheck_clause(B,VN).
typecheck_clause((H :- _),_) :- 
  H =.. [F|_],
  member(F,[def_type,dec_p_type,dec_pp_type]),!,   % reserved words
  print_type_error_clause5(F).
typecheck_clause((H :- B),VN) :- !,
  H =.. [F|P],
  length(P,A),
  functor(H1,F,A),
  (p_type(H1) ->                   % non-polymorphic predicate
     H1 =.. [_|P1],
     mk_dec(P,P1,D),
     setlog:conj_append(D,B,T),
     typecheck_clause(T,VN)        % now a formula (not a clause) is typechecked
  ;
   pp_type(H1,V) ->                % polymorphic predicate
     H1 =.. [_|P1],
     get_type_vars(V,VN,TV),
     mk_dec(P,P1,D),
     maplist(call,TV),
     setlog:conj_append(D,B,T),
     typecheck_clause(T,VN)        % now a formula (not a clause) is typechecked
  ;
   print_type_error_clause3(H)
  ).
typecheck_clause(F,VN) :-          % F is a formula, not a clause
  assert_vars_types(F,VN),
  typecheck_formula(F,VN).


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
% verification of dec constraints
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% checks that each variable in F has exactly one type
% asserts some facts about the types in F
% and makes other consistency checks about types
%
% facts of the form
%   type(V,t)
% are interpreted as
%   "variable V is of type t"
% facts of the form
%   cons_type(u,t)
% are interpreted as
%   "term u is of type t"
% u is the constructor of a sum type
% before asserting type(V,t) or cons_type(u,t), t is checked 
% for consistency
%
assert_vars_types((C & F),VN) :-
  C = dec(V,T), nonvar(V), V = [_|_],!,
  assert_vars_types_list(V,T,VN),
  assert_vars_types(F,VN).
assert_vars_types((C & F),VN) :-
  C = dec(V,T),!,
  expand_type(T,Type),        % in dec(V,T) T is expanded so dec(V,Type) is done
  (var(V),!
   ;
   print_type_error_dec_1(dec(V,Type),VN)
  ),
  (check_type(Type),!,
   assert_fintype(Type)    
   ;
   print_type_error_dec_2(dec(V,Type),VN)
  ),
  get_var(VN,V,Var),
  (\+ type(Var,_),!,           % Var hasn't been declared yet
   assertz(type(Var,Type)),
   assert_vars_types(F,VN)
   ;
   print_type_error_dec_3(dec(V,Type),VN)
  ).
assert_vars_types((C & F),_) :-
  C =.. [F|_],
  member(F,[def_type,dec_p_type,dec_pp_type]),!,   % reserved words
  print_type_error_clause5(F).
assert_vars_types(A,VN) :- 
  A = dec(V,T), nonvar(V), V = [_|_],!,
  assert_vars_types_list(V,T,VN).
assert_vars_types(A,VN) :- 
  A = dec(V,T),!,
  expand_type(T,Type),        % in dec(V,T) T is expanded so dec(V,Type) is done
  (var(V),!
   ;
   print_type_error_dec_1(dec(V,Type),VN)
  ),
  (check_type(Type),!,
   assert_fintype(Type)    
   ;
   print_type_error_dec_2(dec(V,Type),VN)
  ),
  get_var(VN,V,Var),
  (\+ type(Var,_),!,          % Var hasn't been declared yet
   assertz(type(Var,Type))
   ;
   print_type_error_dec_3(dec(V,Type),VN)
  ).
assert_vars_types(A,_) :-
  A =.. [F|_],
  member(F,[def_type,dec_p_type,dec_pp_type]),!,   % reserved words
  print_type_error_clause5(F).
assert_vars_types((_C & F),VN) :- !,
  assert_vars_types(F,VN).
assert_vars_types(_A,_).

assert_vars_types_list([],_,_) :- !.
assert_vars_types_list([X|V],T,VN) :-
  assert_vars_types(dec(X,T),VN),
  assert_vars_types_list(V,T,VN).

check_type(T) :-
  ground(T),                     % types can't have variables
  check_type1(T).

check_type1(T) :-
  atom(T), typedec(T,_),!.
check_type1(T) :-
  T = enum(Enum),!,
  check_type(sum(Enum)).  
check_type1(T) :-
  T = sum(Enum),!,
  (enum(Enum) ->                  % T has already been processed
     true
   ;
   maplist(functor,Enum,H,_),     % H = constructors' heads
   list_to_set(H,H),              % heads can't be repeated
   check_sum(Enum),
   assertz(enum(Enum))            % asserted to simplify some checks
  ).
check_type1(T) :-                 % product type 
  T = [T1,T2|T3],!,
  check_type1(T1),
  check_type1(T2),
  (T3 == [] ->
     true
  ;
   T3 = [T4] ->
     check_type1(T4)
  ;
   check_type1(T3)
  ).
check_type1(T) :-                  % set type
  T = set(S),!,
  check_type1(S).
check_type1(T) :-                  % rel type, it's just a synonym
  T = rel(U,V),!,
  check_type1(set([U,V])).
check_type1(int) :- !.
check_type1(str) :- !.
check_type1(T) :-                  % basic type or built-in type
  atom(T),
  \+ cons_type(T,_),               % T isn't an element of an enum
  (basic(T) ->
     true
   ;
     assertz(basic(T))
  ).

check_sum(Enum) :-
  Enum = [_,_|_],                  % sums have at least 2 elements
  forall(member(E,Enum),check_and_assert_sum_element(E,Enum)).

% (1) and (2) check that E isn't used in other sum
% and if everything goes OK cons_type(E,enum(Enum)) is asserted
% (1) E can't be an element of other sum
% (2) at this point E hasn't be typed so it is.
%     Note that if this clause is called it's because Enum
%     has never be processed
%
check_and_assert_sum_element(E,Enum) :-
  E =.. [H|P],
  \+ member(H,[int,str]),         % int, str can't be elements of a sum
  \+ type(_,H),                   % H isn't another type (*)
  \+ basic(H),
  \+ typedec(H,_),                % H isn't the id of a typedec
  forall(member(X,P),check_type(X)),
  (enum(Enum_),                   % (1)
   expand_type(sum(Enum_),sum(Enum2)),
   Enum2 \== Enum,
   maplist(functor,Enum_,Hs,_),   % H = constructors' heads
   member(H,Hs),!,
   fail
   ;
   assertz(cons_type(E,sum(Enum)))    % (2)
  ).

% assert_fintype(T): if T is a finite type, then assert that fact
assert_fintype(T) :-
  has_finite(T),\+clause(fintype(T),true) ->
       assertz(fintype(T))
  ;
    true.


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
% formula typechecking
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

typecheck_formula((C & F),VN) :- !,
  typecheck_constraint(C,VN),
  typecheck_formula(F,VN).
typecheck_formula(A,VN) :- 
  typecheck_constraint(A,VN).


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
% constraint typechecking
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% declarations are ignored in this phase
typecheck_constraint(dec(_,_),_) :- !.

% meta predicates

typecheck_constraint(neg(P),VN) :- !,
  typecheck_clause(P,VN).

typecheck_constraint((P implies Q),VN) :- !,
  typecheck_clause(P,VN),
  typecheck_clause(Q,VN).

typecheck_constraint((P nimplies Q),VN) :- !,
  typecheck_clause(P,VN),
  typecheck_clause(Q,VN).

typecheck_constraint((P or Q),VN) :- !,
  typecheck_clause(P,VN),
  typecheck_clause(Q,VN).

typecheck_constraint(call(C),VN) :- !,
  typecheck_clause(C,VN).

typecheck_constraint((C)!,VN) :- !,
  typecheck_clause(C,VN).

typecheck_constraint(call(C,_),VN) :- !,
  typecheck_clause(C,VN).
   
typecheck_constraint(solve(C),VN) :- !,
  typecheck_clause(C,VN).
   
typecheck_constraint(delay(C,_),VN) :- !,
  typecheck_clause(C,VN).

typecheck_constraint(bool(_,C),VN) :- !,
  typecheck_clause(C,VN).

% calls to Prolog shouldn't be on constraints
typecheck_constraint(prolog_call(_),_) :- !.

% equality

% equality is polymorphic
typecheck_constraint(X = Y,VN) :- !,
  typecheck_term(X,Tx,VN),
  typecheck_term(Y,Ty,VN),
  (Tx = Ty,!
   ;
   print_type_error(X = Y,VN,Tx,Ty)
  ).
   
typecheck_constraint(X neq Y,VN) :- !,
  typecheck_term(X,Tx,VN),
  typecheck_term(Y,Ty,VN),
  (Tx = Ty,!
   ;
   print_type_error(X neq Y,VN,Tx,Ty)
  ).

% integer constraints

typecheck_constraint(integer(X),VN) :- !,
  typecheck_term(X,T,VN),
  (\+(T == int) ->
     print_type_error(integer(X),VN,T)
   ;
     true
  ).

typecheck_constraint(ninteger(X),VN) :- !,
  typecheck_term(X,T,VN),
  (T == int ->
     print_type_error(ninteger(X),VN,T)
   ;
     true
  ).

typecheck_constraint(X is Y,VN) :- !,
  typecheck_term(X,Tx,VN),
  typecheck_term(Y,Ty,VN),
  (Tx = int, Ty = int,!
   ;
   print_type_error(X is Y,VN,Tx,Ty)
  ).

typecheck_constraint(X =:= Y,VN) :- !,
  typecheck_term(X,Tx,VN),
  typecheck_term(Y,Ty,VN),
  (Tx = int, Ty = int,!
   ;
   print_type_error(X =:= Y,VN,Tx,Ty)
  ).

typecheck_constraint(X =\= Y,VN) :- !,
  typecheck_term(X,Tx,VN),
  typecheck_term(Y,Ty,VN),
  (Tx = int, Ty = int,!
   ;
   print_type_error(X =\= Y,VN,Tx,Ty)
  ).

typecheck_constraint(X =< Y,VN) :- !,
  typecheck_term(X,Tx,VN),
  typecheck_term(Y,Ty,VN),
  (Tx = int, Ty = int,!
   ;
   print_type_error(X =< Y,VN,Tx,Ty)
  ).

typecheck_constraint(X < Y,VN) :- !,
  typecheck_term(X,Tx,VN),
  typecheck_term(Y,Ty,VN),
  (Tx = int, Ty = int,!
   ;
   print_type_error(X < Y,VN,Tx,Ty)
  ).

typecheck_constraint(X >= Y,VN) :- !,
  typecheck_term(X,Tx,VN),
  typecheck_term(Y,Ty,VN),
  (Tx = int, Ty = int,!
   ;
   print_type_error(X >= Y,VN,Tx,Ty)
  ).

typecheck_constraint(X > Y,VN) :- !,
  typecheck_term(X,Tx,VN),
  typecheck_term(Y,Ty,VN),
  (Tx = int, Ty = int,!
   ;
   print_type_error(X > Y,VN,Tx,Ty)
  ).

% set constraints

typecheck_constraint(set(X),VN) :- !,
  typecheck_term(X,T,VN),
  (\+(T = set(_)) ->
     print_type_error(set(X),VN,T)
   ;
     true
  ).

typecheck_constraint(nset(X),VN) :- !,
  typecheck_term(X,T,VN),
  (T = set(_) ->
     print_type_error(nset(X),VN,T)
   ;
     true
  ).

typecheck_constraint(X in Y,VN) :- !,
  typecheck_term(X,Tx,VN),
  typecheck_term(Y,Ty,VN),
  (Ty = set(Tx),!
   ;
   print_type_error(X in Y,VN,Tx,Ty)
  ).

typecheck_constraint(X nin Y,VN) :- !,
  typecheck_term(X,Tx,VN),
  typecheck_term(Y,Ty,VN),
  (Ty = set(Tx),!
   ;
   print_type_error(X nin Y,VN,Tx,Ty)
  ).

typecheck_constraint(disj(X,Y),VN) :- !,
  typecheck_term(X,Tx,VN),
  typecheck_term(Y,Ty,VN),
  (Tx = set(T), Ty = set(T),!
   ;
   print_type_error(disj(X,Y),VN,Tx,Ty)
  ).

typecheck_constraint(ndisj(X,Y),VN) :- !,
  typecheck_term(X,Tx,VN),
  typecheck_term(Y,Ty,VN),
  (Tx = set(T), Ty = set(T),!
   ;
   print_type_error(ndisj(X,Y),VN,Tx,Ty)
  ).

typecheck_constraint(un(X,Y,Z),VN) :- !,
  typecheck_term(X,Tx,VN),
  typecheck_term(Y,Ty,VN),
  typecheck_term(Z,Tz,VN),
  (Tx = set(T), Ty = set(T), Tz = set(T),!
   ;
   print_type_error(un(X,Y,Z),VN,Tx,Ty,Tz)
  ).

typecheck_constraint(nun(X,Y,Z),VN) :- !,
  typecheck_term(X,Tx,VN),
  typecheck_term(Y,Ty,VN),
  typecheck_term(Z,Tz,VN),
  (Tx = set(T), Ty = set(T), Tz = set(T),!
   ;
   print_type_error(nun(X,Y,Z),VN,Tx,Ty,Tz)
  ).

% size

typecheck_constraint(size(X,Y),VN) :- !,
  typecheck_term(X,Tx,VN),
  typecheck_term(Y,Ty,VN),
  (Tx = set(_), Ty = int,!
   ;
   print_type_error(size(X,Y),VN,Tx,Ty)
  ).

typecheck_constraint(nsize(X,Y),VN) :- !,
  typecheck_term(X,Tx,VN),
  typecheck_term(Y,Ty,VN),
  (Tx = set(_), Ty = int,!
   ;
   print_type_error(nsize(X,Y),VN,Tx,Ty)
  ).

% relational constraints

typecheck_constraint(pair(X),VN) :- !,
  typecheck_term(X,T,VN),
  (\+(T = [_,_]) ->
     print_type_error(pair(X),VN,T)
   ;
     true
  ).

typecheck_constraint(npair(X),VN) :- !,
  typecheck_term(X,T,VN),
  (T = [_,_] ->
     print_type_error(npair(X),VN,T)
   ;
     true
  ).

typecheck_constraint(rel(X),VN) :- !,
  typecheck_term(X,T,VN),
  (\+(T = set([_,_])) ->
     print_type_error(rel(X),VN,T)
   ;
     true
  ).

typecheck_constraint(nrel(X),VN) :- !,
  typecheck_term(X,T,VN),
  (T = set([_,_]) ->
     print_type_error(nrel(X),VN,T)
   ;
     true
  ).

typecheck_constraint(id(X,Y),VN) :- !,
  typecheck_term(X,Tx,VN),
  typecheck_term(Y,Ty,VN),
  (Tx = set(T), Ty = set([T,T]),!
   ;
   print_type_error(id(X,Y),VN,Tx,Ty)
  ).

typecheck_constraint(nid(X,Y),VN) :- !,
  typecheck_term(X,Tx,VN),
  typecheck_term(Y,Ty,VN),
  (Tx = set(T), Ty = set([T,T]),!
   ;
   print_type_error(nid(X,Y),VN,Tx,Ty)
  ).

typecheck_constraint(inv(X,Y),VN) :- !,
  typecheck_term(X,Tx,VN),
  typecheck_term(Y,Ty,VN),
  (Tx = set([T,U]), Ty = set([U,T]),!
   ;
   print_type_error(inv(X,Y),VN,Tx,Ty)
  ).

typecheck_constraint(ninv(X,Y),VN) :- !,
  typecheck_term(X,Tx,VN),
  typecheck_term(Y,Ty,VN),
  (Tx = set([T,U]), Ty = set([U,T]),!
   ;
   print_type_error(ninv(X,Y),VN,Tx,Ty)
  ).

typecheck_constraint(comp(X,Y,Z),VN) :- !,
  typecheck_term(X,Tx,VN),
  typecheck_term(Y,Ty,VN),
  typecheck_term(Z,Tz,VN),
  (Tx = set([T,U]), Ty = set([U,V]), Tz = set([T,V]),!
   ;
   print_type_error(comp(X,Y,Z),VN,Tx,Ty,Tz)
  ).

typecheck_constraint(ncomp(X,Y,Z),VN) :- !,
  typecheck_term(X,Tx,VN),
  typecheck_term(Y,Ty,VN),
  typecheck_term(Z,Tz,VN),
  (Tx = set([T,U]), Ty = set([U,V]), Tz = set([T,V]),!
   ;
   print_type_error(ncomp(X,Y,Z),VN,Tx,Ty,Tz)
  ).

% quantifiers and let

% foreach

% (1) variables in X and P are local to the foreach. so the same
%     names can be used in other foreach's with the same or different
%     types. then, after typechecking the inner formula, the type/2
%     facts asserted during this process are retracted. in this way if
%     the same names are used for local variables in a different
%     foreach we don't have a type clash.
typecheck_constraint(foreach(D,F),VN) :- !,
  typecheck_constraint(foreach(D,_,F,true),VN).
typecheck_constraint(foreach(X in Y,P,F1,F2),VN) :- !,
  mk_ris_formula(X in Y,F1,F2,F),
  typecheck_clause(F,VN),
  term_variables([X,P],LocVars),
  forall(member(A,LocVars),(get_var(VN,A,V),retract(type(V,_)),! ; true)). % (1)
% the second argument is _ because typing information
% about these variables is still to be processed
typecheck_constraint(foreach([X|Y],P,F1,F2),VN) :- !,
  setlog:unfold_nested_foreach(foreach([X|Y],P,F1,F2),FEflat),
  FEflat = foreach(A in B,P,FEflat1,FEflat2),
  FEflat_ = foreach(1 in {},P,FEflat1 & A in B,FEflat2),
  typecheck_clause(FEflat_,VN),
  term_variables([X,P|Y],LocVars),
  forall(member(A,LocVars),(get_var(VN,A,V),retract(type(V,_)),! ; true)).

% nforeach

typecheck_constraint(nforeach(X in Y,F),VN) :- !,
  typecheck_constraint(foreach(X in Y,[],F,true),VN).
typecheck_constraint(nforeach(X in Y,P,F1,F2),VN) :- !,
  typecheck_constraint(foreach(X in Y,P,F1,F2),VN).

% exists

% (1) exists calls nforeach with neg(F)
% however, typechecking nforeach and neg(F)
% is the same than typechecking foreach and F
typecheck_constraint(exists(D,F),VN) :- !,
  typecheck_constraint(foreach(D,F),VN).    % (1)
typecheck_constraint(exists(D,P,F1,F2),VN) :- !,
  typecheck_constraint(foreach(D,P,F1,F2),VN).

% nexists
typecheck_constraint(nexists(D,F),VN) :- !,
  typecheck_constraint(foreach(D,F),VN).
typecheck_constraint(nexists(D,P,F1,F2),VN) :- !,
  typecheck_constraint(foreach(D,P,F1,F2),VN).

% let
% typechecking let is similar to typechecking foreach
% (1) variables in P are local to the let. so the same
%     names can be used in other constraints with the same or different
%     types. then, after typechecking the inner formula, the type/2
%     facts asserted during this process are retracted. in this way if
%     the same names are used for local variables in a different
%     constraint we don't have a type clash.
typecheck_constraint(let(P,D,F),VN) :- !,
  mk_ris_formula(1 in {},D,F,NF),     % conjoin D with F, 1 in {} is there just for reuse
  typecheck_clause(NF,VN),
  forall(member(A,P),(get_var(VN,A,V),retract(type(V,_)),! ; true)). % (1)

% user-defined predicates

% polymorphic predicates
% a predicate p of arity n is a polymorphic predicate
% if there is an assertion
%    pp_type(p(T_1,...,T_n))
% where each T_i is either a type or a type-variable. 
% Each t_i is assumed to be the type of the 
% corresponding argument of p.
% For example:
%    pp_type(ran(set([_,U]),set(U)))
%
typecheck_constraint(C,VN) :-
  C =.. [_|P],
  functor(C,F,A),
  functor(T,F,A),
  pp_type(T),!,      % pp_type fact asserted in some consulted file
  typecheck_args_pred(T,P,C,VN).

% non-polymorphic predicates
% a predicate p of arity n is a non-polymorphic predicate
% if there is an assertion:
%    p_type(p(t_1,...,t_n))
% where each t_i is a type. Each t_i is assumed to be 
% the type of the corresponding argument of p.
%
typecheck_constraint(C,VN) :-
  C =.. [_|P],
  functor(C,F,A),
  functor(T,F,A),
  p_type(T),!,      % p_type fact asserted in some loaded file
  typecheck_args_pred(T,P,C,VN).


% {log} commands and special {log} predicates

typecheck_constraint(C,_) :-
    (meta_pred(C),!
    ;
     setlog_command(C),!
    ;
     sys_special(C),!
    ;
     functor(C,F,N),
     sys(F,N)
    ), !.


% predicates of arity 0

typecheck_constraint(C,_) :-
  functor(C,_,0),!.

% all the other constraints fail to typecheck
% so typechecking fails

typecheck_constraint(C,_) :-
  print_type_error_clause3(C).


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
% term typechecking
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% a variable (of any type)
typecheck_term(X,T,VN) :-
  var(X),var(T),!,
  (get_var(VN,X,VarX), type(VarX,T) ->
     true
   ;
     print_type_error_dec_4(X,VN)
  ).
typecheck_term(X,T,VN) :-
  var(X),!,
  (get_var(VN,X,VarX), type(VarX,T1) ->
     (T = T1 ->
        true
     ;
        print_type_error_var(X,T1,T,VN)
     )
   ;
     print_type_error_dec_4(X,VN)
  ).

% integer terms

typecheck_term(E,int,VN) :-
  E = - X,!,
  typecheck_term(X,int,VN).

typecheck_term(E,int,VN) :-
  E = X + Y,!,
  typecheck_term(X,int,VN),
  typecheck_term(Y,int,VN).

typecheck_term(E,int,VN) :-
  E = X - Y,!,
  typecheck_term(X,int,VN),
  typecheck_term(Y,int,VN).

typecheck_term(E,int,VN) :-
  E = X * Y,!,
  typecheck_term(X,int,VN),
  typecheck_term(Y,int,VN).

typecheck_term(E,int,VN) :-
  E = X div Y,!,
  typecheck_term(X,int,VN),
  typecheck_term(Y,int,VN).

typecheck_term(E,int,VN) :-
  E = X mod Y,!,
  typecheck_term(X,int,VN),
  typecheck_term(Y,int,VN).

typecheck_term(X,int,_) :-
  integer(X),!.

% set terms

% extensional
typecheck_term(S,set(T),VN) :-
  S = X with Y, !,
  typecheck_term(Y,T,VN),
  typecheck_term(X,set(T),VN).
typecheck_term(S,set(T),VN) :-
  S = {}(A),!,
  setnotation_to_list(A,Elems,Rest),
  maplist(typecheck_term1(T,VN),Elems),
  typecheck_term(Rest,set(T),VN).

% Cartesian product
typecheck_term(S,set([T,U]),VN) :-
  S = cp(X,Y), !,
  typecheck_term(X,set(T),VN),
  typecheck_term(Y,set(U),VN).

% integer interval
typecheck_term(S,set(int),VN) :-
  S = int(X,Y), !,
  typecheck_term(X,int,VN),
  typecheck_term(Y,int,VN).

% ris
% TODO:
% is the following supported?
%   allow for general control expressions
%   allow for general patterns

% ris(X in Y, formula)
typecheck_term(S,T,VN) :-
  S = ris(X in Y,F),!,
  typecheck_term(ris(X in Y,[],F,X,true),T,VN).
% ris(X in Y, [param], formula)
typecheck_term(S,T,VN) :-
  S = ris(X in Y,V,F), nonvar(V), V = [_|_],!,
  typecheck_term(ris(X in Y,V,F,X,true),T,VN).
% ris(X in Y, formula, pattern)
typecheck_term(S,T,VN) :-
  S = ris(X in Y,F,P),!,
  typecheck_term(ris(X in Y,[],F,P,true),T,VN).
% ris(X in Y, [parm], formula, pattern)
typecheck_term(S,T,VN) :-
  S = ris(X in Y,V,F,P), nonvar(V), V = [_|_],!,
  typecheck_term(ris(X in Y,V,F,P,true),T,VN).
% ris(X in Y, [parm], formula, pattern, formula)
typecheck_term(S,set(T),VN) :-
  S = ris(X in Y,_,F1,P,F2),
  var(P), P == X,!,
  mk_ris_formula(X in Y,F1,F2,F),
  typecheck_clause(F,VN),
  typecheck_term(Y,set(T),VN).
typecheck_term(S,set([T,U]),VN) :-
  S = ris(X in Y,_,F1,P,F2),
  nonvar(P), P = [P1,P2],!, % var(P1), P1 == X,!,
  mk_ris_formula(X in Y,F1,F2,F),
  typecheck_clause(F,VN),
  typecheck_term(Y,set([T,U]),VN),
  typecheck_term(P1,T,VN),
  typecheck_term(P2,U,VN).

% {} is set-polymorphic
typecheck_term(X,set(_),_) :-
  X = {},!.

% ordered pairs / records / lists

typecheck_term(X,T,VN) :- 
  X  = [X1,X2|X3],
  T  = [Tx1,Tx2|Tx3],!,
  typecheck_term(X1,Tx1,VN),
  typecheck_term(X2,Tx2,VN),
  (X3 == [] ->
     Tx3 = []
  ;
   X3 = [X4] ->
     Tx3 = [Tx4],
     typecheck_term(X4,Tx4,VN)
  ;
   typecheck_term(X3,Tx3,VN)
  ).

% strings

typecheck_term(X,str,_) :-
  string(X),!.

% elements of basic types

% in T:X, T is intended to be a basic type
% and X an atom or an integer. in that case T:X is 
% an element of type T. at the type checker level 
% t:m = u:m doesn't type check; t:m=t:n type checks 
% but at the {log} level t:m and t:n are two different 
% terms and so the equality fails, as expected.
%
typecheck_term(T:X,T,VN) :- !,  
  (atom(T), 
   (atom(X),! ; integer(X)),
   \+ cons_type(T,enum(_)) ->
     true
  ;
     print_type_error_elem_ut(T:X,VN)
  ).

% elements of sums

typecheck_term(X,T,VN) :-
  atom(X),!,                        % nullary constructors
  (cons_type(X,T1) ->
     expand_type(T1,T)
  ;
     print_type_error_atom(X,VN)
  ).

typecheck_term(X,T,VN) :-
  functor(X,H,A),                   % non-nullary constructors
  X =.. [H|P],
  functor(Y,H,A),
  Y =.. [H|PY], 
  (cons_type(Y,T1) ->
     expand_type(T1,T),
     maplist(mk_pair,P,PY,LP),
     forall(member([Term,Type],LP),
       (expand_type(Type,EType),typecheck_term(Term,EType,VN))
     )
  ;
     print_type_error_atom(X,VN)
  ),!.   


% here we're sure X isn't of type T
% or X isn't a 'typeable' term
typecheck_term(X,T,VN) :-
  print_type_error_term(X,T,VN).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
% type declarations
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% TODO: throw appropriate exceptions

% (1) Tid can't be the name of a basic type
%     it can be a synonym for int or str
declare_type(Tid,Tdef) :-
  atom(Tid),
  \+ typedec(Tid,_),
  ground(Tdef),
  (atom(Tdef) -> member(Tdef,[int,str]) ; true),  % (1)
  \+ contains_term(Tid,Tdef),
  check_type(Tdef),
  (\+ enum(_),!,
   assertz(typedec(Tid,Tdef))
   ;
   enum(Enum),
   member(Tid,Enum),!,
   fail
   ;
   assertz(typedec(Tid,Tdef))
  ).

% type declaration of user-defined predicates

% (1) more than one dec_p_type for the same p
%     is a sign of a possible error when they
%     are exactly the same
%     if the predicate has more than one clause
%     one dec_p_type is ok
%     note that no exception is risen if there are 
%     two or more p with different arities or with
%     different types (i.e. that kind of polymorphism is ok)
%
declare_p_type(D,VN) :-
  D =.. [_,P],
  (ground(P) ->
     (p_type(P) ->
        print_type_error_clause4(P,VN)         % (1)
     ;
        assertz(p_type(P))
     )
  ;
     print_type_error_clause1(D,VN)
  ).

% dec_pp_type(D,VN) process a pp declaration
% two facts are stored: 
%   pp_type/1 which is exactly P in D =.. [_|P]
%   pp_type/2 which turns type variables in P into
%     constants and stores the constant P and the type
%     variable names
% (1) in the case of polymorphic p's more than
%     one dec_pp_type for the same p is considered
%     an error because the type of polymorphic
%     predicates is given in terms of variables
%
declare_pp_type(D,VN) :-
  D =.. [_,P],
  P =.. [H|A],
  length(A,N),
  functor(F,H,N),
  (pp_type(F) ->
      print_type_error_clause4(P,VN)           % (1)
  ;
      assertz(pp_type(P))
  ),
  term_variables(D,V),
  maplist(call,VN),           % turn type variables into constants
  assertz(pp_type(P,V)).

% only for predicates defined inside {log}
% (e.g. inters, dres, etc.)
% (1) enclosed in dec just to comply with dec_pp_type/2's
%     interface. dec_pp_type/2 will remove dec and will
%     take just D
%
declare_pp_type(D) :-
  declare_pp_type(dec(D),_),              % (1)
  D =.. [H|A],
  length(A,N),
  functor(F,H,N),                     % pp_type/2 facts aren't used in predicates
  retractall(pp_type(F,_)).           % defined inside {log}


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
% consistency of finite types
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% the following predicates ensure the consistency
% between type information and constraint solving
% when finite types are involved
%
% inconsistencies may appear when there are too
% many neq constraints involving variables whose
% types are finite. for example:
%   dec(X,enum([f,t])) & X neq t & X neq f
%   dec([X,Y,Z],enum([f,t])) & X neq Y & X neq Z & Y neq Z
% are unsatisfiable when the typing information is
% considered.
%
% the following predicates turn the above formulas
% into
%   X in {f,t} & X neq t & X neq f
%   X in {f,t} & Y in {f,t} & Z in {f,t} & X neq Y & X neq Z & Y neq Z
%
% variable X is a dec variable if there's a 
% dec(X,_) constraint in scope
% otherwise is a non-dec variable
% non-dec variable appear for example in dom(F,{1})
% because the solution is F = {[1,X]/_} where
% X is non declared (because is new)

% check_finite_types(CS,F)
%   * CS is the constraint store as passed from {log}
%   * F is the formula (list of constraints) built as
%     to ensure consistency
%     {log} must execute F to check consistency
%     F is empty when there's nothing to check (no neq
%     constraints are in CS or their variables aren't
%     of finite types).
%
check_finite_types(CS,F) :-
  (types_ex_vars(CS,EV),
   fintype(_),!,                % if finite types in the formula
   b_getval(vn,VN),
   check_finite_types1(CS,VN,EV,[],F)
  ;
   F = []
  ).

% check_finite_types1(CS,VN,Vars,F)
%   * CS is the constraint store
%   * VN is variable_names as in read_term
%   * Vars is the list of variables participating in
%     neq constraints that have already been processed
%     this is to avoid adding many constraints of the
%     form X in S for each such variable X
%   * F is the formula
% the predicate goes through CS looking for neq constraints
% if there's one it checks whether or not its arguments
% are of a finite type. if not, nothing is done. if they
% are then a constraint of the form X in T is generated
% where X is a variable and T is the set corresponding
% to the type of X. the neq constraints and the
% corresponding "in" constraints are put in F.
%
% TODO: optimization to be done
%       call fintype_to_set only once for each type
%
check_finite_types1([],_,_,_,[]) :- !.
check_finite_types1([C|CS],VN,EV,Vars,F) :-
  is_neq_dec_vars(C,VN,EV,Vars,F0,NewVars),!,
  check_finite_types1(CS,VN,EV,NewVars,F1),
  append(F0,F1,F).
check_finite_types1([C|CS],VN,EV,Vars,F) :-
  is_neq_new_vars(C,VN,EV,Vars,F0,NewVars),!,
  check_finite_types1(CS,VN,EV,NewVars,F1),
  append(F0,F1,F).
check_finite_types1([_|CS],VN,EV,Vars,F) :-
  check_finite_types1(CS,VN,EV,Vars,F).

is_neq_dec_vars(C,VN,EV,Vars,F,NewVars) :- 
   check_finite_types_two_dec_vars(C,VN,EV,X,Y,T),!,  %two variables, at least one a dec variable with a finite type
   mk_neq_in2(Vars,X,Y,T,F,NewVars).

is_neq_dec_vars(C,VN,EV,Vars,F,NewVars) :-
  check_finite_types_dec_var_const(C,VN,EV,X,Y,T),!,   %one dec variable with a finite type, one constant
  mk_neq_in(Vars,X,Y,T,F,NewVars).   % mk_neq_in builds F and NewVars

is_neq_new_vars(C,VN,EV,Vars,F,NewVars) :-
  is_neq(C,_,X,Y),
  var(X),nonvar(Y),!,        % one variable, one constant
  \+get_var(VN,X,_), \+get_type(EV,X,_),    % X is a new variable, we don't know its type
  (Y == {},!,                % Y is the empty set
   F = [X neq Y],
   NewVars = Vars
  ;
   ground(Y),               % Y is a constant
   typecheck_term(Y,T,VN),  % get Y's type; VN shouldn't be necessary (1)
   has_finite(T),
   mk_neq_in(Vars,X,Y,T,F,NewVars)   % mk_neq_in builds F and NewVars
  ).
is_neq_new_vars(C,VN,EV,Vars,F,NewVars) :-
  is_neq(C,_,X,Y),
  var(X),var(Y),                            % two variables
  \+get_var(VN,X,_), \+get_type(EV,X,_),    % X is a new variable
  \+get_var(VN,Y,_), \+get_type(EV,Y,_),    % Y is a new variable
  find_var(X,VN,Z = Term),
  type(Z,T),                % Z is a dec var, then it has a type
  get_type_from_term(X,Term,T,Tx),
  has_finite(Tx),
  mk_neq_in2(Vars,X,Y,Tx,F,NewVars).

mk_neq_in(Vars,X,Y,T,F,NewVars) :-
  (\+setlog:member_strong(X,Vars),!,
   fintype_to_set(T,L),
   setlog:mk_set(L,S),
   F = [X neq Y,X in S],
   NewVars = [X|Vars]
  ;
   F = [X neq Y],
   NewVars = [X|Vars]
  ).

% mk_neq_in2 is similar to mk_neq_in
% TODO: check if mk_neq_in2 is enough and mk_neq_in
%       can be deleted
%
mk_neq_in2(Vars,X,Y,T,F,NewVars) :-
  (\+setlog:member_strong(X,Vars),
   \+setlog:member_strong(Y,Vars),!,
   fintype_to_set(T,L),
   setlog:mk_set(L,S),
   F = [X neq Y,X in S,Y in S],
   NewVars = [X,Y|Vars]
  ;
   \+setlog:member_strong(X,Vars),!,
   fintype_to_set(T,L),
   setlog:mk_set(L,S),
   F = [X neq Y,X in S],
   NewVars = [X|Vars]
  ;
   \+setlog:member_strong(Y,Vars),!,
   fintype_to_set(T,L),
   setlog:mk_set(L,S),
   F = [X neq Y,Y in S],
   NewVars = [Y|Vars]
  ;
   F = [X neq Y],
   NewVars = Vars
  ).

check_finite_types_two_dec_vars(C,VN,EV,X,Y,T) :-    
  is_neq(C,_,X,Y),
  var(X),var(Y),        % two variables
  (get_var(VN,X,Vx),!,  % X is dec variable and its name is Vx
   type(Vx,T),          % the type of Vx (i.e. X) is T, so is Vy's
   fintype(T)           % T is a finite type
  ;                     % or
   get_var(VN,Y,Vy),!,  % Y is a dec variable and its name is Vy
   type(Vy,T),          % the type of Vy (i.e. Y) is T, so is Vx's
   fintype(T)           % T is a finite type
  ;                     % or
   get_type(EV,X,T),!   % X is a dec variable, T is its (finite) type
  ;                     % or
   get_type(EV,Y,T)     % Y is a dec variable, T is its (finite) type
  ).

check_finite_types_dec_var_const(C,VN,EV,X,Y,T) :-   
  is_neq(C,_,X,Y),
  var(X),ground(Y),     % one variable, one constant
  (get_var(VN,X,V),!,   % X is a dec variable and its name is V
   type(V,T),           % the type of X is T
   fintype(T)           % T is a finite type
  ;
   get_type(EV,X,T)     % X is a dec variable, T is its (finite) type
  ).

% types_ex_vars(CS,EV)
%  goes through the constraint store CS looking for
%  dec constraints. this is necessary when user-defined
%  predicates contain existential variables. typing of
%  these variables has been checked when the predicate
%  was consulted but this information was lost after
%  that. so in order to check finite type consistency
%  we need to reconstruct that information. this is a
%  price to pay if types are checked only at consult
%  time. EV is a list of pairs [V,T] where V is a
%  variable in a dec and T is a finite type.
%
types_ex_vars([],[]) :- !.
types_ex_vars([dec(V,T)|CS],EV) :- 
  expand_type(T,Type),
  (clause(fintype(Type),true) ->
       true       
  ;
       has_finite(Type),
       assertz(fintype(Type)),
       (Type = enum(Enum) ->
           check_sum(Enum)
       ;
           true
       )
  ),!,
  mk_list_types(V,Type,V_EV),
  types_ex_vars(CS,EV1),
  append(V_EV,EV1,EV).
types_ex_vars([_|CS],EV) :-
  types_ex_vars(CS,EV).

mk_list_types(V,T,EV) :-
  var(V),!,
  EV = [[V,T]].
mk_list_types([],_,[]) :- !.
mk_list_types(L,T,EV) :- 
  L = [V|Vars],!,
  (var(V),!,
   EV = [[V,T]|EV1],
   mk_list_types(Vars,T,EV1)
  ;
   mk_list_types(Vars,T,EV)
  ).
mk_list_types(_,_,[]).

% get_type(EV,X,T)
%   * EV is the list returned by types_ex_vars
%   * X is a variable
%   * T is the type of X according to EV
% if X is not the first component of any pair in EV
% get_type fails 
%
get_type([[V,T]|_],X,T) :-
  V == X,!.
get_type([[_,_]|DEC],X,T) :-
  get_type(DEC,X,T).


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
% grounding -- generation of typed constants
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% gen_typed_eq(NonIntVar,NeqConst,VN,L,N,EqOther)
% - NonIntVar list of variables for which a value has
%   to be generated
% - NeqConst list of constants which the generated
%   constants can't belong to
% - VN variable names as in read_term
% - L label (letter) to be used as a prefix for some
%   constants
% - N start number to label some constants
% - EqOther list of X = t or X in S (t and S ground)
% this predicate generates the constants to be bound
% to the variables in NonIntVar.
% the constants generated by gen_typed_eq have the
% following form:
% - int -> 0,1,-1,2,-2,...
% - str -> n0, n1, n2,....
% - basic type t -> t:n0, t:n1, t:n2,...
% - sum types -> nullary constructs -> themselves
%                non-nullary construct x(T) -> x(c) where c:T
% - product type [T,U] -> [ct,cu] where ct:T and cu:U
% - set type set(T) -> {c} where c:T
%
%(the next numbers refer to the code of gen_typed_eq/6)
% (1) this is different from the untyped case due
%     to the presence of finite types. we can't
%     just generate a different constant for
%     each variable of a finite type because
%     there might not be enough of them.
%     ex: dec([X,Y,Z],enum([a,b])) & X neq Y & X neq Z.
%     we can't generate three different values
%     for X, Y and Z. we have two chose the same
%     value for two of them. however,
%     at this point we know the formula is
%     satisfiable because check_finite_types has
%     been called, so there are enough values of
%     type T as to satisfy the formula. then for
%     this case we generate set membership
%     constraints for each variable of type T.
%     the solver will assign a value to each
%     variable.
% (2) this can be improved. T is converted once
%     for each variable of type T. actually, S
%     has been computed a few processing steps
%     before when check_finite_types was called.
% (3) the constant for the next variable will be
%     different from the constants for the
%     previous variables because there might be
%     neq constraints involving the variables in
%     NonIntVar.
gen_typed_eq([],_,_,_,_,[]) :- !.
gen_typed_eq([X|NonIntVar],NeqConst,VN,L,N,EqOther) :-
  get_var(VN,X,V),!,        % X is a dec variable
  type(V,T),
  (is_finite(T) ->          % (1)
     fintype_to_set(T,TL),  % (2)
     setlog:mk_set(TL,S),
     N1 is N + 1,
     gen_typed_eq(NonIntVar,NeqConst,VN,L,N1,EqOther1),
     EqOther = [X in S | EqOther1]
  ;
     gen_typed_val(T,L,N,Val),  % T is infinite
     (member(Val,NeqConst) ->   % increase N until a valid constant is found
        N1 is N + 1,
        gen_typed_eq([X|NonIntVar],NeqConst,VN,L,N1,EqOther)
     ;
        N1 is N + 1,  % (3) 
        gen_typed_eq(NonIntVar,NeqConst,VN,L,N1,EqOther1),
        EqOther = [X = Val | EqOther1]
     )
  ).
% (1) X isn't a dec variable so is part of the r.h.s.
%     of an equality in VN
% (2) TODO: this part until the end is equal to the
%     previous clause. it can/should be put in one new
%     predicate.
gen_typed_eq([X|NonIntVar],NeqConst,VN,L,N,EqOther) :-
  find_var(X,VN,Z = Term),  % (1)
  type(Z,T),                % Z is a dec var, then it has a type
  get_type_from_term(X,Term,T,Tx),
  (is_finite(Tx) ->         % (2)
     fintype_to_set(Tx,TL),
     setlog:mk_set(TL,S),
     N1 is N + 1,
     gen_typed_eq(NonIntVar,NeqConst,VN,L,N1,EqOther1),
     EqOther = [X in S | EqOther1]
  ;
     gen_typed_val(Tx,L,N,Val),
     (member(Val,NeqConst) ->
        N1 is N + 1,
        gen_typed_eq([X|NonIntVar],NeqConst,VN,L,N1,EqOther)
     ;
        N1 is N + 1,
        gen_typed_eq(NonIntVar,NeqConst,VN,L,N1,EqOther1),
        EqOther = [X = Val | EqOther1]
     )
  ).

% gen_typed_val(T,L,N,Val)
% - T is a type
% - L label (letter) to be used as a prefix for some
%   constants
% - N number to label some constants
% - Val is the generated constant
% only non-recursive types are considered because
% if the term is an ordered pair, we generate a
% value for each of its components; if the term
% is a set, we generate a value for each of its
% elements. however, if the type is a sum such
% that one of its constructors has an argument
% of a set or product type then we need to 
% generate values for that type too.
%
% values of basic types
gen_typed_val(T,L,N,CT) :-
  atom(T),
  \+member(T,[int,str]),!,
  atomic_list_concat([T,:,L,N],C),
  atom_to_term(C,CT,_).
% values of type int
gen_typed_val(int,_,N,N) :- !.
% values of type str
gen_typed_val(str,L,N,S) :-
  atomic_list_concat([L,N],C),
  atom_string(C,S),!.
% values of sum types
% if the constructors of the sum type are exhausted
% then no value for that type can be generated and
% so the formula would be unsatisfiable but at this
% point we know the formula is satisfiable. so the
% case sum([_|_]) is the only to be considered.
%
% first we try to find an infinite constructor.
% if we do, we use these values because there
% are infinitely many of them.
% if we don't, the sum type is finite and so it
% must be one of the components of a product
% type where the other component must be infinite
% because otherwise the whole type would be 
% finite and so the first branch of gen_typed_eq
% would have been executed.
%
% no infinite constructor has been found so we
% use the last one (which might be infinite)
% TODO: the first and last clauses are equal
gen_typed_val(sum([C]),L,N,Val) :-
  C =.. [H|P],
  gen_typed_val_list(P,L,N,PVal), 
  Val1 =.. [H|PVal],
  Val = Val1.
% try to find an infinite constructor
gen_typed_val(sum([C|Cons]),L,N,Val) :-
  C =.. [_|P],
  is_finite(P),!,  % P is a product type
  gen_typed_val(sum(Cons),L,N,Val).
% an infinite constructor has been found
gen_typed_val(sum([C|_]),L,N,Val) :-
  C =.. [H|P],
  gen_typed_val_list(P,L,N,PVal),
  Val1 =.. [H|PVal],
  Val = Val1.
%
% the following two clauses are used when a
% constructor of a sum type depends on a product
% or set type.
%
% note that only singleton sets are returned.
% the justification is as follows. set(T) is
% part of a constructor of a sum type. if the 
% sum type is finite then it's part of a
% infinite product type (otherwise the whole
% type would be finite and so the first
% branch of gen_typed_eq would have been
% executed), so we can generate infinite
% constants of the product type by using
% the other component. otherwise the sum type
% is infinite. so either T is infinite or
% there's another infinite constructor in the
% sum type. in either case we can generate
% infinitely many constants (e.g. infinitely
% many singleton sets of type T).
% 
gen_typed_val(set(T),L,N,Val) :- !,
  gen_typed_val(T,L,N,Val1),
  Val = {} with Val1.
gen_typed_val([T,U],L,N,Val) :-
  gen_typed_val(T,L,N,Val1),
  gen_typed_val(U,L,N,Val2),
  Val = [Val1,Val2].

% gen_typed_val_list(TypeL,L,N,ValL)
gen_typed_val_list([],_,_,[]) :- !.
gen_typed_val_list([T|TypeL],L,N,ValL) :-
  gen_typed_val(T,L,N,Val),
  gen_typed_val_list(TypeL,L,N,ValL1),
  ValL = [Val | ValL1].


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
% user commands
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

setlog_command(idef_type(_,_)) :- !.
setlog_command(reset_types) :- !.
setlog_command(type_of(_)) :- !.
setlog_command(type_decs(_)) :- !.
setlog_command(expand_type(_,_)) :- !.

ssolve_command(idef_type(ID,T)) :- !,    %% declare or consult a type
    dec_type(ID,T).
ssolve_command(reset_types) :- !,        %% delete all type declarations since
    reset_types.                       
ssolve_command(type_of(P)) :- !,         %% prints the type of predicate P
    type_of(P).
ssolve_command(type_decs(T)) :- !,       %% lists all type declarations
    type_decs(T).
ssolve_command(expand_type(T,ET)) :- !,  %% expands type T in ET
    expand_type(T,ET).

dec_type(I,T) :-
  nonvar(T),!,
  declare_type(I,T).
dec_type(I,T) :-
  atom(I),!,
  (typedec(I,T) ->
     true
  ;
     print_type_error_dec_type(I)
  ).

reset_types :-
  retractall(type(_,_)), 
  retractall(cons_type(_,_)), 
  retractall(enum(_)), 
  retractall(p_type(_)), 
  retractall(pp_type(_)), 
  retractall(pp_type(_,_)),
  retractall(typedec(_,_)),
  retractall(fintype(_)),
  retractall(basic(_)),
  dec_internal.

type_of(P) :-
  atom(P),!,
  current_functor(P,A),
  functor(F,P,A),
  nl,
  (p_type(F) ->
     write(F)
   ;
   pp_type(F) ->
     numbervars(F,19,_),
     write(F)
   ;
     print_type_error_clause3(F)
  ),
  nl.

type_decs(T) :-
  (T == td ->
     listing(typedec(_,_))
   ;
   T == pt ->
     listing(p_type(_))
   ;
   T == ppt ->
     listing(pp_type(_))
   ;
     throw(setlog_excpt("possible arguments are td, pt or ppt"))
   ).


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
% initialization
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% retract all type facts of previous runs of the 
% typechecker.
% load the type definitions of defined constraints
% implemented inside {log} (e.g. inters, dom, etc.)

:- initialization(reset_types).


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
% auxiliary predicates
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% get_var(VN,V,X)
%   VN is variable_names as in read_term
%   V is a variable
%   X = inv(VN)(V)
%
get_var([],_,_) :- !, fail.   
get_var([X = Y|_],V,Var) :-
  Y == V,!,
  Var = X.
get_var([_ = Y|VN],V,Var) :-
  \+(Y == V),
  get_var(VN,V,Var).

% get_type_vars(V,VN,TV)
%   V is a list of the form ['X','Y','Z',...]
%   VN is variable_names as in read_term
%   dres(V,VN,TV)
%
get_type_vars([],_,[]) :- !.
get_type_vars([X|V],VN,TV) :- 
  get_type_vars1(X,VN,E) ->
    TV = [E|TV1],
    get_type_vars(V,VN,TV1)
  ;
    get_type_vars(V,VN,TV).    

get_type_vars1(X,[X1 = Y|VN],E) :- 
  X == X1 ->
    E = (X = Y)
  ;
    get_type_vars1(X,VN,E).

% mk_dec(V,T,D)
% V = [V_1,...,V_n], T = [T_1,...,T_n] 
% ==> D = dec(V_1,T_1) & ... & dev(V_n,T_n)
% if V_i is twice only one dec is conjoined
% TODO: implement with maplist?
%
mk_dec([],[],true) :- !.
mk_dec([V|Vars],[_|Types],Conj) :-
  setlog:member_strong(V,Vars),!,
  mk_dec(Vars,Types,Conj).
mk_dec([V|Vars],[T|Types],dec(V,T) & D) :-
  mk_dec(Vars,Types,D).

mk_ris_formula(F1,F2,F3,F) :-
  setlog:conj_append(F1,F2,G),
  setlog:conj_append(G,F3,F).

typecheck_args_pred(Pred,Args,C,VN) :-
  Pred =.. [_|DTypes],
  length(DTypes,N),
  length(ExpTypes,N),
  maplist(expand_type,DTypes,ExpTypes),
  (typecheck_args_pred1(Args,ATypes,VN) ->
    (ExpTypes = ATypes ->
       true
     ;
       print_type_error_defcons1(C,ATypes,Pred,VN)
    )
   ;
     print_type_error_defcons2(C,VN)
  ).

typecheck_args_pred1([],[],_) :- !.
typecheck_args_pred1([X|P],ATypes,VN) :-
  typecheck_term(X,Tx,VN),
  expand_type(Tx,ETx),
  ATypes = [ETx|Types],
  typecheck_args_pred1(P,Types,VN).

typecheck_term_args(A,T,VN) :- 
  nonvar(A), A=(A1,A2),!,
  typecheck_term(A1,T,VN),
  typecheck_term_args(A2,T,VN).
typecheck_term_args(A1,T,VN) :- 
  typecheck_term(A1,T,VN).

% expand_type(T,ET)
% recursively expands type T following type declarations
% possibly occurring in T
% For example:
%   dec_type(a,[b,c]).
%   dec_type(t,set(a)).
% then
%   expand_type(set(t),set(set([b,c])))
%
expand_type(T,T) :-
  var(T),!.
expand_type(enum(L),sum(L)) :- !.
expand_type(sum(L),ET) :- !,
  expand_type_sum(L,LE),
  ET = sum(LE).
expand_type(T,ET) :-
  atom(T),!,
  (typedec(T,TD) ->
     expand_type(TD,ET)
  ;
     ET = T
  ).     
expand_type(set(T),ET) :- !,    
  expand_type(T,ET1),
  ET = set(ET1).
expand_type(rel(T,U),ET) :-  !,     % rel type; synonym for set
  expand_type(set([T,U]),ET).
expand_type([T|T1],ET) :-  !,   
  expand_type(T,ET1),
  expand_type(T1,ET2),
  ET = [ET1|ET2].
expand_type([],[]).

expand_type_sum([],[]).
expand_type_sum([C|R],[CE|RE]) :-
  C =.. [H|P],
  maplist(expand_type,P,PE),
  CE =.. [H|PE],
  expand_type_sum(R,RE).

% find_diff1(L1,L2,L3,N)
% must be always invoked with N = 1
% L1 and L2 are assumed to be lists of the same length
% nth1(K,L1,E1) & nth1(K,L2,E2) & E1 \= E2
% <==> member([K,E1,E2],L3) 
% for any K in [1,length(L1)]
%
find_diff1([],[],[],_) :- !.
find_diff1([X|L1],[X|L2],L3,N) :-
  !,
  M is N + 1,
  find_diff1(L1,L2,L3,M).
find_diff1([X|L1],[Y|L2],[[N,X,Y]|L3],N) :-
  M is N + 1,
  find_diff1(L1,L2,L3,M).

% is meant to be used from maplist
% in this way each element of the list
% goes in the last argument (Term)
%
typecheck_term1(Type,VN,Term) :-
  typecheck_term(Term,Type,VN).

% transforms the set notation (1,2/R) or (1/{2/R})
% into the list L and the rest R
% setnotation_to_list((1,2/R),[1,2],R)
% the caller eliminated {} from (1,2/R); i.e.
% the caller had {1,2/R} but passed just (1,2/R)
%
setnotation_to_list(S,L,R) :-
  nonvar(S), S = (X,Y),!,
  L = [X|L1],
  setnotation_to_list(Y,L1,R).
setnotation_to_list(E,[E],{}) :-
  var(E),!.
setnotation_to_list(E,L,R) :-
  E = (X/Y),!,
  L = [X],
  R = Y.
setnotation_to_list(E,[E],{}).

% predicates used by {log}

remove_dec(X,X) :-           % var
    var(X),!.
remove_dec(X,X) :-           % constant terms
    atomic(X),!.
remove_dec(X,Z) :-           % dec/2 atoms
    X = (dec(_,_) & F),!,
    remove_dec(F,Z).
remove_dec(X,true) :-        % dec/2 atoms
    X = dec(_,_),!.
remove_dec(X,Z) :-           % all other terms
    =..(X,[F|ListX]),
    remove_dec_all(ListX,ListZ),
    =..(Z,[F|ListZ]).

remove_dec_all([],[]).
remove_dec_all([A|L1],[B|L2]) :-
    remove_dec(A,B),
    remove_dec_all(L1,L2).

% ignore type declarations or remove variable 
% declarations from ordinary goals
ignore_type_dec(Goal,Term) :-        
  (Goal =.. [F|_],
   member(F,[def_type,dec_p_type,dec_pp_type]) ->
      Term = (:- true)
  ;
      %remove_dec(Goal,Goal1),
      %Term = (:- Goal1)
      Term = (:- Goal)   
  ).


% is_finite(T) iff T is a finite type
% T is a finite type iff
%  * T is an enumerated type (i.e. a sum type with only nullary constructors)
%  * T is the sum of finite types
%  * T is the product of finite types
%  * T is the powerset of a finite type
%
is_finite(enum(_)) :- !.
is_finite(sum(C)) :- !,
  is_finite_sum(C).  
is_finite([]) :- !.          % the base case for a product type
is_finite([T1|T]) :-  !,   
  is_finite(T1),
  is_finite(T).
is_finite(set(T)) :-    !,   
  is_finite(T).  
is_finite(rel(T,U)) :-       % rel type; synonym for set
  is_finite(set([T,U])).  

is_finite_sum([]).
is_finite_sum([C|R]) :-
  C =.. [_|P],
  forall(member(T,P),is_finite(T)),
  is_finite_sum(R).

% has_finite(T) iff T is a finite type
% T has a finite type iff
%  * T is an enumerated type (i.e. a sum type with only nullary constructors)
%  * T is the sum of finite types
%  * T is the product of at least one finite type
%    dec(F,rel(enum([t,f]),int)) & 
%    pfun(F) & F = {X1,X2,X3} & X1 neq X2 & X1 neq X3 & X2 neq X3 &
%    dec([X1,X2,X3],[enum([t,f]),int])
%  * T is the powerset of a finite type
%
has_finite(enum(_)) :- !.
has_finite(sum(C)) :- !,
  has_finite_sum(C).  
has_finite([T]) :-            % the base case for a product type
  has_finite(T),!.
has_finite([T1|T]) :-  !,   
  (has_finite(T1),!
  ;
   has_finite(T)
  ).
has_finite(set(T)) :-    !,   
  has_finite(T).  
has_finite(rel(T,U)) :-       % rel type; synonym for set
  has_finite(set([T,U])).  

has_finite_sum([]).
has_finite_sum([C|R]) :-
  C =.. [_|P],
  forall(member(T,P),has_finite(T)),
  has_finite_sum(R).

% fintype_to_set(Type,Set)
% writes finite type Type as {log} set term Set
%
fintype_to_set(enum(Elems),Elems) :- !.    % enumerated type
fintype_to_set(sum(C),Elems) :- !,
  fintype_to_set_sum(C,Elems).
fintype_to_set([],[]) :- !.                % product type
fintype_to_set(P,CP) :-                    % product type
  P = [T,U],!,                             %   two types (base case)
  fintype_to_set(T,ST),
  fintype_to_set(U,SU),
  findall([X,Y],(member(X,ST),member(Y,SU)),CP).
fintype_to_set([T|P],CP) :- !,             % product type
  fintype_to_set(T,ST),                    %   more than two types
  fintype_to_set(P,CPP),
  findall([X,Y],(member(X,ST),member(Y,CPP)),CP1),
  flatten_elem(CP1,CP).
fintype_to_set(set(T),PS) :- !,            % set type
  fintype_to_set(T,S),
  findall(X,(setlog:powerset(S,E),setlog:mk_set(E,X)),PS).
fintype_to_set(rel([T,U]),PS) :-         % rel type; it's just a synonym
  fintype_to_set(set([T,U]),PS).

fintype_to_set_sum([],[]) :- !.   
fintype_to_set_sum([C|R],[C|Elems]) :-
  atom(C),!,                             % nullary constructor
  fintype_to_set_sum(R,Elems).
fintype_to_set_sum([C|R],Elems) :-
  C =.. [H|P],
  (P = [sum(Elems2)],!,                  % unary constructor
   fintype_to_set_sum(Elems2,ElemsP)
  ;
   fintype_to_set(P,ElemsP)              % binary or more constructor
  ),
  apply_cons(H,ElemsP,ElemsCons),        % apply_cons(b,[x,y],[b(x),b(y)])
  fintype_to_set_sum(R,Elems1),
  append(Elems1,ElemsCons,Elems).

% apply_cons(H,L,T)
% if L = [L1,...,LN] then T = [H(L1),...,H(LN)]
% apply_cons(b,[x,y],[b(x),b(y)])
% apply_cons(b,[[x,y],[u,v],[b(x,y),b(u,v)])
apply_cons(_,[],[]) :- !.
apply_cons(C,[E|R],[T|RT]) :-
  (atom(E) ->                   % unary constructor
     T =.. [C,E]                % apply_cons(b,[x,y],[b(x),b(y)])
  ;
     T =.. [C|E]                % binary or more constructor
  ),                            % apply_cons(b,[[x,y],[u,v],[b(x,y),b(u,v)])
  apply_cons(C,R,RT).

% flatten_elem(NL,FL)
%   flattens each element of NL and puts the result
%   in FL
% it's called only when the elements of NL are
% lists of lists. for example if NL = [[1,2],[a,b]]
% flatten_elem isn't called; if NL = [[[1,2],0],[[a,b],k]]
% it is called and the result is FL = [[1,2,0],[a,b,k]]
%
flatten_elem([],[]) :- !.
flatten_elem([E|NL],FL) :-
  flatten_elem(NL,FL1),
  flatten(E,FE),
  FL = [FE|FL1].

mk_pair(X,Y,[X,Y]).

% find_var(Var,VN,Eq)
% - Var is a variable
% - VN is variable_names as in read_term
% - Eq is the element in VN where Var is at the right-hand side
%
% Var must be somewhere in VN, so VN = [] isn't considered
%
find_var(Var,[X = Term|_],X = Term) :- 
 term_variables(Term,Vars),
 setlog:member_strong(Var,Vars),!. 
find_var(Var,[_|VN],Eq) :- 
 find_var(Var,VN,Eq).
 
% get_type_from_term(X,Term,T,Tx)
% - X is a var
% - Term is a typed term; X is part of Term
% - T is the type of Term
% - Tx is the type of X deduced from Term and T
%
% the search is made by means of structural induction
% over the form of T
% only some cases are considered because the
% others are impossible at this point
%
get_type_from_term(X,Term,T,T) :-       % if Term is X, T is X's type
  var(Term),
  X == Term,!.
get_type_from_term(X,Term,T,Tx) :-      % Term is an ordered pair
  T = [TTerm1,TTerm2],!,                % iff T is a product type
  nonvar(Term),
  Term = [Term1,Term2],
  (get_type_from_term(X,Term1,TTerm1,Tx),!
  ;
   get_type_from_term(X,Term2,TTerm2,Tx)
  ).
get_type_from_term(X,Term,T,Tx) :-      % Term is a set
  T = set(TElem),                       % iff T is a set type
  nonvar(Term),
  Term = Set with E,!,
  (get_type_from_term(X,E,TElem,Tx),!
  ;
   get_type_from_term(X,Set,T,Tx)
  ).



%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
% type error messages
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

print_type_error(C,VN,Tx) :-
   term_string(C,S1,[variable_names(VN)]),
   C =.. [_,X],
   term_string(X,S2,[variable_names(VN)]),
   term_string(Tx,S3),
   string_concat("type error: in ",S1,C1),
   string_concat(C1,"\n\t",C11),
   string_concat(C11,S2,C2),
   string_concat(C2," is of type ",C3),
   string_concat(C3,S3,C4),
   throw(setlog_excpt(C4)).

print_type_error(C,VN,Tx,Ty) :-
   term_string(C,S1,[variable_names(VN)]),
   C =.. [_,X,Y],
   term_string(X,S2,[variable_names(VN)]),
   term_string(Tx,S3),
   term_string(Y,S4,[variable_names(VN)]),
   term_string(Ty,S5),
   string_concat("type error: in ",S1,C1),
   string_concat(C1,"\n\t",C11),
   string_concat(C11,S2,C2),
   string_concat(C2," is of type ",C3),
   string_concat(C3,S3,C4),
   string_concat(C4,"\n\t",C5),
   string_concat(C5,S4,C6),
   string_concat(C6," is of type ",C7),
   string_concat(C7,S5,C8),
   throw(setlog_excpt(C8)).

print_type_error(C,VN,Tx,Ty,Tz) :-
   term_string(C,S1,[variable_names(VN)]),
   C =.. [_,X,Y,Z],
   term_string(X,S2,[variable_names(VN)]),
   term_string(Tx,S3),
   term_string(Y,S4,[variable_names(VN)]),
   term_string(Ty,S5),
   term_string(Z,SZ1,[variable_names(VN)]),
   term_string(Tz,SZ2),
   string_concat("type error: in ",S1,C1),
   string_concat(C1,"\n\t",C11),
 
   string_concat(C11,S2,C2),
   string_concat(C2," is of type ",C3),
   string_concat(C3,S3,C40),

   string_concat(C40,"\n\t",C41),
   string_concat(C41,S4,C42),
   string_concat(C42," is of type ",C43),
   string_concat(C43,S5,C4),

   string_concat(C4,"\n\t",C5),
   string_concat(C5,SZ1,C6),
   string_concat(C6," is of type ",C7),
   string_concat(C7,SZ2,C8),
   throw(setlog_excpt(C8)).

print_type_error_var(X,T1,T,VN) :-
   term_string(X,S1,[variable_names(VN)]),
   term_string(T1,S2,[variable_names(VN)]),
   term_string(T,S3,[variable_names(VN)]),
   string_concat("type error: variable ",S1,C1),
   string_concat(C1," has type ",C2),
   string_concat(C2,S2,C3),
   string_concat(C3," but it should be ",C4),
   string_concat(C4,S3,C5),
   throw(setlog_excpt(C5)).

print_type_error_dec_1(D,VN) :-
   term_string(D,S1,[variable_names(VN)]),
   D =.. [_,V,_],
   term_string(V,S2,[variable_names(VN)]),
   string_concat("type error: in ",S1,C1),
   string_concat(C1,", ",C11),
   string_concat(C11,S2,C2),
   string_concat(C2," is not a variable",C3),
   throw(setlog_excpt(C3)).

print_type_error_dec_2(D,VN) :-
   term_string(D,S1,[variable_names(VN)]),
   D =.. [_,_,T],
   term_string(T,S2,[variable_names(VN)]),
   string_concat("type error: in ",S1,C1),
   string_concat(C1,", type ",C11),
   string_concat(C11,S2,C2),
   string_concat(C2," is not well-defined",C3),
   throw(setlog_excpt(C3)).

print_type_error_dec_3(D,VN) :-
   term_string(D,S1,[variable_names(VN)]),
   D =.. [_,V,_],
   term_string(V,S2,[variable_names(VN)]),
   string_concat("type error: in ",S1,C1),
   string_concat(C1,", ",C11),
   string_concat(C11,"variable ",C12),
   string_concat(C12,S2,C2),
   string_concat(C2," is already declared",C3),
   throw(setlog_excpt(C3)).

print_type_error_dec_4(X,VN) :-
   term_string(X,S1,[variable_names(VN)]),
   string_concat("type error: variable ",S1,C1),
   string_concat(C1," has no type declaration",C3),
   throw(setlog_excpt(C3)).

print_type_error_defcons1(C,ATypes,T,VN) :-
   term_string(C,S1,[variable_names(VN)]),
   string_concat("type error: in ",S1,C1),
   string_concat(C1," arguments have the wrong type:\n",C2),
   T =.. [_|Types],
   length(Types,N),
   length(ETypes,N),
   maplist(expand_type,Types,ETypes),
   find_diff1(ATypes,ETypes,Diff,1),
   copy_term(Types,CTypes),
   C =.. [_|P],
   mk_msg(Diff,P,VN,Msg),
   string_concat(C2,Msg,C7),
   term_variables(CTypes,VT),
   (VT == [] ->
      throw(setlog_excpt(C7))
   ;
      string_concat(C7," for some types ",C8),
      numbervars(VT,19,_),
      term_string(VT,S5,[numbervars(true)]),
      string_concat(C8,S5,C9),   
      throw(setlog_excpt(C9))
   ).

mk_msg([],_,_,"") :- !.
mk_msg([[N,T1,T2]|L],P,VN,Msg) :-
  nth1(N,P,A),
  term_string(A,Sa,[variable_names(VN)]),
  term_string(T1,S1),
  numbervars(T2,19,_),
  term_string(T2,S2,[numbervars(true)]),
  string_concat(Sa," is ",C1),
  string_concat(C1,S1,C2),
  string_concat(C2," but should be ",C3),
  string_concat(C3,S2,C4),
  (L \== [] -> 
     string_concat(C4,"\n",C5)
  ;
     C5 = C4
  ),
  mk_msg(L,P,VN,Msg1),
  string_concat(C5,Msg1,Msg).

print_type_error_defcons2(C,VN) :-
   term_string(C,S1,[variable_names(VN)]),
   string_concat("type error: in ",S1,C1),
   string_concat(C1," one of the arguments has the wrong type",C2),
   throw(setlog_excpt(C2)).
   
print_type_error_clause1(H,VN) :-
   term_string(H,S1,[variable_names(VN)]),
   string_concat("type error: type declaration of predicate ",S1,C1),
   string_concat(C1," include variables",C2),
   throw(setlog_excpt(C2)).

print_type_error_clause2(B,VN) :-
   term_string(B,S1,[variable_names(VN)]),
   string_concat("type error: type declaration of predicate ",S1,C1),
   string_concat(C1," must have exactly one parameter",C2),
   throw(setlog_excpt(C2)).

print_type_error_clause3(H) :-
   H =.. [F|P],
   length(P,A),
   term_string(F,S1),
   term_string(A,S2),
   string_concat("type error: type declaration of predicate ",S1,C1),
   string_concat(C1,"/",C2),
   string_concat(C2,S2,C3),
   string_concat(C3," is missing",C4),
   throw(setlog_excpt(C4)).

print_type_error_clause4(H,VN) :-
   term_string(H,S1,[variable_names(VN)]),
   string_concat("type error: more than one type declaration for predicate ",S1,C1),
   throw(setlog_excpt(C1)).

print_type_error_clause5(H) :-
   term_string(H,S1),
   string_concat("type error: ",S1,C1),
   string_concat(C1," is a reserved predicate; can't be used in this context",C2),
   throw(setlog_excpt(C2)).

print_type_error_dec_type(D,VN) :-
   term_string(D,S1,[variable_names(VN)]),
   string_concat("type error: incorrect type declaration ",S1,C1),
   throw(setlog_excpt(C1)).

print_type_error_atom(A,VN) :-
   term_string(A,S,[variable_names(VN)]),
   string_concat("type error: '",S,C1),
   string_concat(C1,"' doesn\'t fit in the sum type",C2),
   throw(setlog_excpt(C2)).

print_type_error_dec_type(ID) :-
   term_string(ID,S),
   string_concat(S," isn't a type identifier",C),
   throw(setlog_excpt(C)).

print_type_error_term(X,T,VN) :-
   var(T),!,
   term_string(X,Sx,[variable_names(VN)]),
   string_concat("type error: ",Sx,C1),
   string_concat(C1," isn't an admissible term in type-checking mode",C2),
   throw(setlog_excpt(C2)).
print_type_error_term(X,T,VN) :-           % not sure if this branch is possible
   term_string(X,Sx,[variable_names(VN)]),
   term_string(T,St),
   string_concat("type error: the type of ",Sx,C1),
   string_concat(C1," isn't ",C2),
   string_concat(C2,St,C3),
   throw(setlog_excpt(C3)).

print_type_error_elem_ut(T:X,VN) :-
   term_string(T:X,S1,[variable_names(VN)]),
   string_concat("type error: ",S1,C1),
   string_concat(C1," isn't well defined",C2), 
   throw(setlog_excpt(C2)).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
% type definitions for {log} derived constraints
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

dec_internal :-
% inters
  declare_pp_type(inters(set(T),set(T),set(T))),

% subset
  declare_pp_type(subset(set(T),set(T))),

% diff
  declare_pp_type(diff(set(T),set(T),set(T))),

% sdiff
  declare_pp_type(sdiff(set(T),set(T),set(T))),

% less
  declare_pp_type(less(set(T),T,set(T))),

% dom
  declare_pp_type(dom(set([T,_]),set(T))),

% dompf
  declare_pp_type(dompf(set([T,_]),set(T))),

% ran
  declare_pp_type(ran(set([_,U]),set(U))),

% dres
  declare_pp_type(dres(set(T),set([T,U]),set([T,U]))),

% dares
  declare_pp_type(dares(set(T),set([T,U]),set([T,U]))),

% rres
  declare_pp_type(rres(set([T,U]),set(U),set([T,U]))),

% rares
  declare_pp_type(rares(set([T,U]),set(U),set([T,U]))),

% rimg
  declare_pp_type(rimg(set([T,U]),set(T),set(U))),

% oplus
  declare_pp_type(oplus(set([T,U]),set([T,U]),set([T,U]))),

% pfun
  declare_pp_type(pfun(set([_,_]))),

% apply
  declare_pp_type(apply(set([T,U]),T,U)),

% comppf
  declare_pp_type(comppf(set([T,U]),set([U,V]),set([T,V]))),

% applyTo
  declare_pp_type(applyTo(set([T,U]),T,U)),

% smin
  declare_pp_type(smin(set(int),int)),

% smax
  declare_pp_type(smax(set(int),int)),

% negations

% ninters
  declare_pp_type(ninters(set(T),set(T),set(T))),

% nsubset
  declare_pp_type(nsubset(set(T),set(T))),

% ndiff
  declare_pp_type(ndiff(set(T),set(T),set(T))),

% nsdiff
  declare_pp_type(nsdiff(set(T),set(T),set(T))),

% ndom
  declare_pp_type(ndom(set([T,_]),set(T))),

% ndompf
  declare_pp_type(ndompf(set([T,_]),set(T))),

% nran
  declare_pp_type(nran(set([_,U]),set(U))),

% ndres
  declare_pp_type(ndres(set(T),set([T,U]),set([T,U]))),

% ndares
  declare_pp_type(ndares(set(T),set([T,U]),set([T,U]))),

% nrres
  declare_pp_type(nrres(set([T,U]),set(T),set([T,U]))),

% nrares
  declare_pp_type(nrares(set([T,U]),set(T),set([T,U]))),

% nrimg
  declare_pp_type(nrimg(set([T,U]),set(T),set(U))),

% noplus
  declare_pp_type(noplus(set([T,U]),set([T,U]),set([T,U]))),

% npfun
  declare_pp_type(npfun(set([_,_]))),

% napply
  declare_pp_type(napply(set([T,U]),T,U)),

% ncomppf
  declare_pp_type(ncomppf(set([T,U]),set([U,V]),set([T,V]))),

% napplyTo
  declare_pp_type(napplyTo(set([T,U]),T,U)).


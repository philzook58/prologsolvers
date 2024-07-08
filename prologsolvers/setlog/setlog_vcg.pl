% setlog_vcg-1.3d

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%                                                %
%                                                %
%     Verification Condition Generator (VCG)     %
%                                                %
%   for {log} programs modeling state machines   %
%                                                %
%                                                %
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% A {log} program representing a state machine is
% composed of a set of (non-recursive) clauses and
% facts. All these clauses and facts are
% assumed to be bundled in a single file. 
%
% A {log} program representing a state machine
% may start by declaring one or more parameters
% Parameters are declared by means of a 
% "parameters" fact:
%
% parameters([list_of_variables]).
%
% - All the elements of the list must be distinct
%   variables.
% - Axioms, state operations and state invariants
%   may use these variables (same names).
%
% Example:
%
% parameters([A,B]).
%
% Following the parameters declaration there may
% be zero or more axioms. Axioms are predicates
% depending only on parameters. Each such axiom
% must be preceded by an "axiom" fact:
%
% axiom(axiom_name)
%
% where axiom_name must coincide with the head of 
% the predicate stating the axiom. 
%
% Example:
%
% axiom(ax1).
% ax1(A) :- 0 =< A.
%
% Axiom arguments can only be program parameters.
%
% Following the axioms there must be a "variables"
% fact:
%
% variables([list_of_variables]).
%
% - All the elements of the list must be distinct
%   variables.
% - The list of variables must be disjoint w.r.t.
%   the list of parameters.
% - These variables represent the state variables.
% - State operations and state invariants must use
%   these variables (same names).
% - After-state variables in state operations must
%   be the same variables ending in "_" (i.e., the
%   primed variables).
%
% Example:
%
% variables([A,B]).
%
% Following the "variables" fact there may
% be zero or more state invariants. Each such 
% invariant must be preceded by an "invariant"
% fact:
%
% invariant(inv_name).
%
% where inv_name must coincide with the head of 
% the predicate stating the invariant. 
%
% Example:
%
% invariant(inv1).
% inv1(A) :- 0 =< A.
%
% Invariant arguments can be state variables (at
% least one of them) and other parameters of the
% program.
%
% After the invariants there may be an "initial"
% fact declaring the presence of a predicate
% stating initial conditions for the program.
%
% initial(init_name).
%
% where init_name must coincide with the head of
% the predicate stating the initial conditions.
% This predicate is called the "initial state".
%
% Example:
%
% initial(init).
% init(A,B) :- 0 =< A & B = {}.
%
% Initial state arguments can be state variables
% (at least one of them) and other parameters of
% the program.
%
% Finally, after the initial state declaration it
% may follow zero or more state operations. Each
% state operation must be preceded by an
% "operation" fact.
%
% operation(oper_name).
%
% where oper_name must coincide with the head of
% the predicate stating the operation.
%
% Example:
%
% operation(op).
% op(A,B,A_,B_) :- A_ is A + 2 & B_ = {A_/B}.
%
% Operation arguments can be the state variables
% (at least one of them), input variables, output
% variables and other parameters of the program.
% If V is a state variable and V_ is an argument
% of an operation then V must be another argument.
% Including V_ as an argument when V isn't a
% state variable is an error. Including V_, when
% V is a state variable, more than once is an
% error. If V is a state variable it can be
% included at most two times in the head of the
% operation.
%
% If V is a state variable and we declare p(V,V)
% to be an operation then it is interpreted as p
% not modifying the value of V; p(V) is
% interpreted as p not modifying the value of V,
% as well. On the other hand, if we declare
% p(V,V_) it's interpreted as p possibly
% changing V's value. 
%
% These are examples of right and wrong operation
% heads assuming the following fact:
% 
% variables([A,B]).
%
% oper(C) --> error, A or B missing
% oper(A) --> oper doesn't change A nor B
% oper(A,I,A) --> ok, oper doesn't change A nor B
% oper(A,I,A_) --> ok, oper changes A but not B
% oper(A,B,I,A) --> oper doesn't change A nor B
% oper(A,B,I,A,B_) --> ok, oper doesn't change A,
%                      but changes B
% oper(A,B,A_,B_,A_) --> error A_ more than once
% oper(A,A,A) --> error A more than twice
%
% If an invariant, initial or operation fact is
% given, the next predicate (not a directive)
% must be the declared one.
%
% Example:
%
% invariant(inv1).
% p(A) :- ...
% inv1(A,B) :- ...
%
% is wrong because p is a predicate between the
% invariant fact declaring inv1 and inv1's
% definition.
%
% However, between an invariant, initial or
% operation fact and the corresponding
% predicate there can be other facts.
%
% Example:
%
% invariant(q).
% dec_p_type(q(set(int))).
% q(B) :- B neq {}.
%
% And between a predicate and the next invariant,
% initial or operation fact there can be other
% predicates.
%
% Example:
%
% variables([A,B]).
% p(A) :- A = 4.     % p is an auxiliary predicate
% invariant(q).
% dec_p_type(q(set(int))).
% q(B) :- B neq {}.
% w(A) :- A neq 5.   % w is an auxiliary predicate
% operation(z).
% z(A,A_) :- w(A) & A_ is A - 2.
%
% variables, invariant, initial and operation 
% must be in that order.
%
% Although many are optional it is expected that
% any non-trivial program has at least one 
% invariant, an initial state and one operation.
%
% Given such a {log} program VCG generates the
% following verification conditions:
%
% - The initial state satisfies each and every
%   invariant.
%
%       ini(V1,...Vn) & inv_1(X1,...,Xm)
%       ...............................
%       ini(V1,...Vn) & inv_k(X1,...,Xm)
%
% - If there's no initial state, each invariant is
%   satisfiable.
%
%       inv_1(X1,...,Xm)
%       ................
%       inv_k(X1,...,Xm)
%
% - Each operation is satisfiable.
%
%       oper_1(V11,...,V1n)
%       ...................
%       oper_m(Vm1,...,Vmn_m)
%
% - Each operation preservers each invariant.
%
%     neg(inv(V1,...,Vn) & 
%         oper(X1,...,Xm) implies 
%         inv(V1_,...,Vn_)
%     )
%
%   If an operation doesn't change the value of
%   any state variable on which an invariant
%   depends, a trivial VC is generated in that
%   case.
%
%   Example:
%
%   variables([A,B]).
%   invariant(inv1).
%   inv1(A) :- ...
%   invariant(inv2).
%   inv2(B) :- ...
%   operation(op).
%   op1(A,A_) :- ...
%   op2(A,B,A_,B) :- ...
%
%   Then op1 and op2 trivially preserve inv2, so
%   trivial invariance lemmas are generated for
%   op1 and op2 w.r.t. inv2.
%
% - axiom_wd and inv_wd VC's are also generate
%   (search "wd" for more documentation)
%
% - the conjunction of all axioms is satisfiable
%
% The VC's for a program saved in file p.pl or 
% p.slog are written in a file called p-vc.pl
% p-vc.slog
%

% maybe part of the following code should be removed when VCG is
% integrated into {log}

:- use_module(library(strings)).

% vcg(Spec)
% reads file Spec, check some consistency conditions
% and generates the corresponding vc's.
% if errors are found the analysis of the file continues
% and vc's are generated for the right parts.
% vc's are saved in a file named Spec-vc.pl (or .slog)
% Spec-vc.pl is overwritten without warning
%

vcg(Spec) :-
  retractall(dparameters(_)),
  retractall(dtheorem(_,_,_)),
  retractall(daxiom(_,_,_)),
  retractall(dvariables(_)),
  retractall(vc_sat(_)),
  retractall(vc_unsat(_,_,_,_,_,_)),
  retractall(dinvariant(_,_,_)),
  retractall(doperation(_)),
% tab is used for pretty-printing vc's code
  b_setval(tab,"  "),
% disables singleton variables warning
% will be restored after processing a parameters or variables declaration
% a parameters or variables declaration always contains singleton variables
  style_check(-singleton),
% step records the current processing step w.r.t to
% directives
% none -> parameters -> variables -> axiom -> invariant -> initial -> operation
  b_setval(step,none),
  (exists_file(Spec) ->
     open(Spec,read,SpecStream)
  ;
     print_notfile(Spec),
     fail
  ),
  vc_file_stream(Spec,VCStream),!,
  vc_preamble(Spec,VCStream),
  read_loop_vcg(SpecStream,VCStream),
  b_getval(step,Step),
  (Step \== operation -> print_no_operation ; true),
  vc_epilogue(Spec,VCStream),
  VCStream = [[_,VCFile],[_,VCAll]|_],
  close(SpecStream),
  close(VCFile),
  close(VCAll).

% read_loop_vcg read clauses from SpecStream until
% a variables, invariant, initial or operation fact
% is found in which case it calls the function that
% process the corresponding fact.
%
read_loop_vcg(SpecStream,VCStream) :-
  read_clause(SpecStream,Clause,[variable_names(VN)]),
  (Clause \== end_of_file ->
     (Clause =.. [H|P],
      member(H,
             [parameters,
              variables,axiom,invariant,initial,operation,theorem]),!,
      (P = [ID], nonvar(ID) ->              % our facts have exactly 1 argument
         process_clause(H,ID,SpecStream,VN,VCStream)
      ;
         print_wrong_declaration(H)
      )
     ;
      true
     ),
     read_loop_vcg(SpecStream,VCStream) ; true
  ).
%
% end code to be removed

% (1) ID is the name of the axiom, Ax is the head of
%     the axiom (including its arguments), VN are the
%     variable names as in read_term
% (2) a satisfiability vc is a predicate that is expected
%     to be satisfiable.
% (3) an unsatisfiability vc is a predicated that is
%     expected to be unsatisfiable
%     ID is the name of the vc, Type states whether the vc
%     was generated due to an axiom or an invariant, AI is
%     the name of the axiom or invariant involved in the 
%     vc, L is ID plus the arguments,
%     Op is the operation involved in the vc and VN are
%     the variable names as in read_term
% (5) ID is the name of the invariant, Inv is the head of
%     the invariant (including its arguments), VN are the
%     variable names as in read_term
% (6) ID is the name of the theorem, Th is the head of
%     the clause defining the theorem and VN are the 
%     variable names as in read_term
%
:- dynamic(dparameters/1). % parameters with their user names
:- dynamic(daxiom/3).      % axiom(ID,Ax,VN) (1)
:- dynamic(dvariables/1).  % state-variables with their user names
:- dynamic(vc_sat/1).      % satisfiability vc's (2)
:- dynamic(vc_unsat/6).    % unsatisfiability vc's (3)
:- dynamic(dinvariant/3).  % invariant(ID,Inv,VN) (5)
:- dynamic(doperation/1).  % names of operations
:- dynamic(all_unsat_vc/6).
:- dynamic(dtheorem/3).    % user-defined theorems (6)
:- dynamic(unsat_sol/5).

%
% process parameters
%
process_clause(parameters,SV,_,VN,_) :-
  b_getval(step,S),
  (S == none ->                    % parameters comes first
     check_parameters(SV,Error),
     (Error = ok ->
        assertz(dparameters(VN)),
        b_setval(step,parameters) ; true
     )
  ;
     print_wrong_order(parameters)
  ).
%
% process variables
%
process_clause(variables,SV,_,VN,_) :-
  style_check(-singleton),
  b_getval(step,S),
  (member(S,[none,parameters]) ->
     check_variables(SV,Error),
     (Error = ok ->
        assertz(dvariables(VN)),
        b_setval(step,variables) ; true
     ),
     style_check(+singleton)   % singleton variables check is restored
  ;
     print_wrong_order(variables)
  ).
%
% process axiom
%
process_clause(axiom,AX,File,_,Out) :-
  (\+daxiom(AX,_,_) ->                     % axiom is unique
    b_getval(step,S),
    (member(S,[variables,axiom]) ->
       b_setval(step,axiom),
       % read until the axiom; else is an error
       search_clause(File,AX,Axiom,VN,Err1),
       (Err1 == ok ->
         (Axiom =.. [AX | Params] ->
            check_axiom(AX,Params,VN,Err2),
            (Err2 == ok ->
               Out = [_,[_,VCAll]|_],
               term_string(Axiom,SAxiom,[variable_names(VN)]),
               format(VCAll,"daxiom(~s,~s).~n",[AX,SAxiom]),
               assertz(daxiom(AX,Axiom,VN)),
               generate_vc(axiom_wd,Out,Axiom,VN)
            ;
               true
            )
         ;
            print_miss_dir(AX,Axiom)
         ) ; true
       )
    ;
       print_wrong_order(axiom)
    )
  ;
    print_dup_dir(AX)
  ).
%
% process invariant
%
process_clause(invariant,IN,File,_,Out) :-
  (\+dinvariant(IN,_,_) ->                  % invariant is unique
    b_getval(step,S),
    (S == axiom ->
        % generate_vc for axioms is called now
        % because it involves the conjunction
        % of all axioms, so it can't be called
        % during axiom processing at this
        % point all axioms should have been
        % declared and stated in this case
        % it's run only when the 1st invariant
        % is processed
        generate_vc(axioms_sat,Out); true
    ),
    (member(S,[variables,axiom,invariant]) ->    % invariant after var or ax
       (member(S,[variables,axiom]) -> 
          b_setval(step,invariant) ; true
       ),
       % read until the invariant; else is an error
       search_clause(File,IN,Inv,VN,Err1),
       (Err1 == ok ->
         (Inv =.. [IN | Params] ->
            check_invariant(IN,Params,VN,Err2),
            (Err2 == ok ->
               Out = [_,[_,VCAll]|_],
               term_string(Inv,SInv,[variable_names(VN)]),
               format(VCAll,"dinvariant(~s,~s).~n",[IN,SInv]),
               assertz(dinvariant(IN,Inv,VN)),
               generate_vc(inv_wd,Out,Inv,VN)
            ;
               true
            )
         ;
            print_miss_dir(IN,Inv)
         ) ; true
       )
    ;
       print_wrong_order(invariant)
    )
  ;
    print_dup_dir(IN)
  ).
%
% process the initial state
%
process_clause(initial,IN,File,_,Out) :-
  b_getval(step,S),
  (member(S,[variables,invariant]) ->      % initial goes after var or inv
     b_setval(step,initial),               % only one initial allowed
     % read until the initial; else is an error
     search_clause(File,IN,Ini,VN,Err1),
     (Err1 == ok ->
       (Ini =.. [IN | Params] ->
          check_initial(IN,Params,VN,Err2),
          (Err2 == ok -> 
             generate_vc(inv_sat_ini,Out,Ini,VN) ; true
          )
       ;
        print_miss_dir(IN,Ini)
       ) ; true
     )
  ;
   print_wrong_order(initial)
  ).
%
% process operations
%
process_clause(operation,ON,File,_,Out) :-
  (\+doperation(ON) ->                               % operation is unique
    b_getval(step,S),
    (S = operation ->
       % read until the operation; else is an error
       search_clause(File,ON,Oper,VN,Err1),
       (Err1 == ok ->
         (Oper =.. [ON | Params] ->
            check_operation(ON,Params,VN,Err2),
            (Err2 == ok -> 
               assertz(doperation(ON)),
               generate_vc(operation,Out,Oper,VN) ; true
            )
         ;
          print_miss_dir(ON,Oper)
         ) ; true
       ) ; true
    ),
    (S == invariant ->                               % no initial defined
       b_setval(step,operation),
       generate_vc(inv_sat,Out,_,_),                 % vc's for invariants now
       process_clause(operation,ON,File,_,Out) ; true 
    ),
    (member(S,[variable,initial]) ->                 % operation after initial
       b_setval(step,operation),
       process_clause(operation,ON,File,_,Out) ; true 
    )
  ;
    print_dup_dir(ON)
  ).
%
% process theorems
%
process_clause(theorem,Th,File,_,Out) :-
  (\+dtheorem(Th,_,_) ->                         % theorem is unique
    b_getval(step,S),
    (member(S,[axiom,invariant,operation]) ->    % theorem during any of these
       % read until the theorem; else is an error
       search_clause(File,Th,Thrm,VN,Err1),
       (Err1 == ok ->
         (Thrm =.. [Th | Params] ->
            check_theorem(Th,Params,VN,Err2),
            (Err2 == ok ->
               assertz(dtheorem(Th,Thrm,VN)),
               generate_vc(theorem,Out,Thrm,VN)
            ;
               true
            )
         ;
            print_miss_dir(Th,Thrm)
         ) ; true
       )
    ;
       print_wrong_order(theorem)
    )
  ;
    print_dup_dir(Th)
  ).

% search_clause(FileStream,Dir,Head,VN,Error)
% reads clauses until one of the form (Head :- _) is found
% VN is the variable_names read by read_clause
% Dir is used to print errors
% Error reifies the predicate
%
search_clause(FileStream,Dir,Head,VN,Error) :-
  read_clause(FileStream,Clause,[variable_names(VN1)]),
  (Clause = (Head1 :- _) ->
     term_string(Head1,SHead,[variable_names(VN1)]),
     term_string(Head,SHead,[variable_names(VN)]),
     Error = ok
  ;
     Clause =.. [H | _],
     (member(H,[variables,invariant,initial,operation,end_of_file]) ->
        print_unexpected_clause(Dir,H),
        Error = err
     ;
        search_clause(FileStream,Dir,Head,VN,Error)
     )
  ).


% TODO check existence of new file
% finish if it does, print message
%
vc_file_stream(Spec,VCFile) :-
  sub_atom(Spec,I,_,_,'.pl'),!,
  sub_atom(Spec,0,I,_,File1),
  atom_concat(File1,'-vc.pl',File2),
  open(File2,write,VCFile1),
  atom_concat(File1,'-all.pl',File3),
  open(File3,write,VCFile2),
  VCFile = [[File2,VCFile1],[File3,VCFile2]].
vc_file_stream(Spec,VCFile) :-
  sub_atom(Spec,I,_,_,'.slog'),!,
  sub_atom(Spec,0,I,_,File1),
  atom_concat(File1,'-vc.slog',File2),
  open(File2,write,VCFile1),
  atom_concat(File1,'-all.pl',File3),
  open(File3,write,VCFile2),
  VCFile = [[File2,VCFile1],[File3,VCFile2]].


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%                                                %
%                                                %
%            Consistency checking                %
%                                                %
%                                                %
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% check_parameters(SV)
% SV must be a list of distinct variables
%
check_parameters(SV,E) :-
  check_only_one_clause(parameters,parameters,1),
  check_variables2(SV,E,parameters).


% check_axiom(AX,Params,VN,Error)
% AX is the axiom name (i.e. :- axiom(IN))
% Params is the list of arguments of the axiom
% only parameters are allowed in Params
% if all checks are passed, Error = ok; otherwise Error = err
%
check_axiom(AX,Params,VN,Error) :-
   length(Params,L),
   check_only_one_clause(axiom,AX,L),
   (dparameters(PV) ->
      only_parameters(AX,VN,PV,Params,Error)
   ;
      Error = err,
      print_no_param
   ).


% check_variables(SV)
% SV must be a list of distinct variables (check_variables2)
% SV and the parameters (if any) are disjoint (check_variables1)
check_variables(SV,E) :-
  check_only_one_clause(variables,variables,1),
  check_variables2(SV,E1,variables),
  (E1 == ok ->
     (dparameters(PV) ->
        check_variables1(SV,PV,E2),
        E2 = E
     ;
        E = ok
     )
  ;
     E = E1
  ).


% check_variables1(SV,PV)
% SV and PV are disjoint
check_variables1([],_,ok) :- !.
check_variables1([X = _ | SV],PV,E) :-
  (memberchk(X = _,PV) ->
     check_variables1(SV,PV,E)
  ;
     print_var_param,
     E = err
  ).


% check_variables2(SV,E,S)
% SV are only variables
% no element in SV is repeated
check_variables2([],ok,_) :- !.
check_variables2([V|SV],E,S) :-
  (var(V),!,
   (\+setlog:member_strong(V,SV),!,
    check_variables2(SV,E,S)
   ;
    print_dup_var(S),
    E = err
   )
  ;
    print_only_vars(S,V),
    E = err
  ).

% check_invariant(IN,Params,VN,Error)
% IN is the invariant name (i.e. :- invariant(IN))
% Params is the list of arguments of the invariant
% only variables are allowed in Params
% at least one element of Params must be a state variable
% if all checks are passed, Error = ok; otherwise Error = err
%
check_invariant(IN,Params,VN,Error) :-
  length(Params,L),
  check_only_one_clause(invariant,IN,L),
  dvariables(SV),
  (dparameters(PV) ->
     only_param_state(IN,VN,SV,PV,Params,Error)
  ;
     only_param_state(IN,VN,SV,[],Params,Error)
  ).

% check_initial(Params,VN,Params_)
% for now checks the same than invariant
%
check_initial(IN,Params,VN,Error) :-
  check_invariant(IN,Params,VN,Error).

% check_operation(ON,Params,VN,E)
% ON is the operation name (i.e. :- operation(ON))
% Params is the list of arguments of the operation
% only variables are allowed in Params
% at least one element of Params must be a state variable
% unprimed and primed state variables must verify some
% conditions documented in check_oper_vars/5 below
% if all checks are passed, Error = ok; otherwise Error = err
%
check_operation(ON,Params,VN,Error) :-
  length(Params,L),
  check_only_one_clause(operation,ON,L),
  all_vars(ON,Params,Error1),                     % checks the first condition
  (Error1 == ok ->
     dvariables(SV),
     one_state_var(ON,VN,SV,Params,Error2),       % checks the second condition
     (Error2 == ok -> 
        check_oper_vars(ON,VN,SV,Params,Error3),  % checks the third condition
        Error = Error3
     ;
        Error = Error2
     )  
  ; 
     Error = Error1
  ).


% check_theorem(Th,Params,VN,Error)
% Th is the theorem name (i.e. theorem(Th))
% Params is the list of arguments of the theorem
% only variables are allowed in Params
% if all checks are passed, Error = ok; otherwise Error = err
%
check_theorem(Th,Params,_,Error) :-
  length(Params,L),
  check_only_one_clause(theorem,Th,L),
  all_vars(Th,Params,Error).


% checks that the keywords of the language
% have only one clause. for example, if
% p/6 is declared as an operation, there can
% be only one clause of the form p/6
check_only_one_clause(KW,AX,L) :-
  functor(Pred,AX,L),
  findall(_,setlog:isetlog(Pred :- _,usr),Bag),
  length(Bag,LBag),
  (LBag > 1 -> print_in_spec(KW,AX,L) ; true).


% all_vars(T,L,E)
% true if L is a list of variables
% if true E=ok, else E=err
all_vars(_,[],ok) :- !.
all_vars(T,[V|Vars],E) :-
  (var(V) ->
     all_vars(T,Vars,E)
  ;
     print_only_vars(T,V),
     E = err
  ).


% one_state_var(T,VN,SV,L,E)
% T is the name of the operation
% VN is variable_names as in read_term
%   these are the arguments of T
% SV is variable_names as in read_term
%   these are the state variables
% L is a list of variables
% true if exists V in L such that
%   inv(VN)(V) in dom(SV)
% E = ok if true; E = err if false
%
one_state_var(T,_,_,[],err) :-
  !,
  print_no_stateVariable(T).
one_state_var(T,VN,SV,[V|Vars],E) :-
   setlog:get_var(VN,V,X),
   (is_var_name(SV,X) ->
      E = ok
   ;
      one_state_var(T,VN,SV,Vars,E)
   ).

% only_parameters(T,VN,PV,L,E)
% T is the name of a predicate
% VN is variable_names as in read_term
%   these are the arguments of T
% PV is variable_names as in read_term
%   these are the parameters
% L is a list of variables
% true if for all V in L
%   inv(VN)(V) in dom(PV)
% E = ok if true; E = err if false
%
only_parameters(_,_,_,[],ok) :- !.
only_parameters(T,VN,PV,[V|Vars],E) :-
  (var(V) ->
     setlog:get_var(VN,V,X),
     (is_var_name(PV,X) ->
        only_parameters(T,VN,PV,Vars,E)
     ;
        print_not_param(T,X),
        E = err
     )  
  ;
     print_only_vars(T,V),
     E = err
  ).


% only_param_state(T,VN,SV,PV,L,E)
% T is the name of a predicate
% VN is variable_names as in read_term
%   these are the arguments of T
% SV is variable_names as in read_term
%   these are the state variables
% PV is variable_names as in read_term
%   these are the parameters
% L is a list of variables
% true if for all V in L
%   inv(VN)(V) in dom(SV) u dom(PV)
% E = ok if true; E = err if false
%
only_param_state(_,_,_,_,[],ok) :- !.
only_param_state(T,VN,SV,PV,[V|Vars],E) :-
  (var(V) ->
     setlog:get_var(VN,V,X),
     (is_var_name(SV,X) ->
        only_param_state(T,VN,SV,PV,Vars,E)
     ;
       (is_var_name(PV,X) ->
          only_param_state(T,VN,SV,PV,Vars,E)
       ;
          print_only_params_state(T,X),
          E = err
       )
     )
  ;
     print_only_vars(T,V),
     E = err
  ).

% check_oper_vars(T,VN,SV,L,E)
% T is the name of a predicate
% VN is variable_names as in read_term
%   these are the arguments of T
% SV is variable_names as in read_term
%   these are the state variables
% L is a list of variables
% true if for each V in L such that V is in SV
% then V is at most once more in L (i.e. repeated before state var
%                                   indicating unchanged variable) or 
% V_ is only once in L, (i.e. V is at most twice in L or V and V_ are in L)
% if V_ is in L then V must be in SV
% E = ok if true; E = err if false
%
check_oper_vars(_,_,_,[],ok) :- !.
check_oper_vars(T,VN,SV,[V|Vars],E) :-
  (var(V) ->
     (after_state(VN,SV,V,AX) ->          % V after state var
        (setlog:member_strong(V,Vars) ->  % after state var twice
           print_too_many(T,AX),
           E = err
        ;
           (get_before_state(VN,AX,BV) ->
              remove_var_single(Vars,V,Vars1),
              remove_var_single(Vars1,BV,Vars2),
              (setlog:member_strong(BV,Vars2) ->  % still before state
                 setlog:get_var(SV,BV,BX),
                 print_too_many(T,BX),
                 E = err
              ;
                 check_oper_vars(T,VN,SV,Vars2,E)
              )
           ;
              print_state_var_miss(T,AX),
              E = err           
           )
        )
     ;
        (before_state(VN,SV,V,BX) ->
           (get_after_state(VN,BX,AV) ->
              remove_var_single(Vars,AV,Vars1),
              check_oper_vars(T,VN,SV,[AV,V|Vars1],E)
           ;
              remove_var_single(Vars,V,Vars1),    % no after state var
              (setlog:member_strong(V,Vars1) ->   % before var twice(unchanged)
                 remove_var_single(Vars1,V,Vars2),
                 (setlog:member_strong(V,Vars2) -> % still before var
                    print_too_many(T,BX),
                    E = err
                 ;
                    check_oper_vars(T,VN,SV,Vars2,E)
                 )
              ;
                 check_oper_vars(T,VN,SV,Vars1,E)
              )
           )
        ;
           check_oper_vars(T,VN,SV,Vars,E)         % V is not a state variable
        )
     )
  ;
     print_only_vars(T,V),
     E = err
  ).

% after_state(VN,SV,V,AX)
% true is V is an after state variable in which case
% AX is the external name (atom) of V
% VN is variable_names as in read_term
%   these are the arguments of T
% SV is variable_names as in read_term
%   these are the state variables
% 
after_state(VN,SV,V,AX) :-
  setlog:get_var(VN,V,AX),
  atom_string(AX,SX),
  string_concat(S1,"_",SX),      % looks like V is an after-state variable
  atom_string(BX,S1),            % BX is before-state variable name
  is_var_name(SV,BX).            % OK, V is an after-state variable

% before_state(VN,SV,V,BX)
% true is V is a state variable in which case
% BX is the external name (atom) of V
% VN is variable_names as in read_term
%   these are the arguments of T
% SV is variable_names as in read_term
%   these are the state variables
% 
before_state(VN,SV,V,BX) :-
  setlog:get_var(VN,V,BX),
  is_var_name(SV,BX).            % OK, V is a state variable

% get_after_state(VN,BX,AV)
% BX is an atom corresponding to a state variable
% true if the corresponding after state variable
% is in VN, in which case AV is that variable
% VN is variable_names as in read_term
%   these are the arguments of T
% SV is variable_names as in read_term
%   these are the state variables
% 
get_after_state(VN,BX,AV) :-
   atom_string(BX,SBX),
   string_concat(SBX,"_",SAX),
   atom_string(AX,SAX),
   member(AX = AV,VN).   
  

% get_before_state(VN,AX,BV)
% AX is an atom corresponding to an after state variable
% true if the corresponding state variable
% is in VN, in which case BV is that variable
% VN is variable_names as in read_term
%   these are the arguments of T
% SV is variable_names as in read_term
%   these are the state variables
%
get_before_state(VN,AX,BV) :-
   atom_string(AX,SAX),
   string_concat(SBX,"_",SAX),
   atom_string(BX,SBX),
   (member(BX = BV,VN),! ; BV = _).
  

is_var_name([],_) :- !, fail.
is_var_name([X = _|_],V) :-
  X == V,!.
is_var_name([X = _|VN],V) :-
  X \== V,
  is_var_name(VN,V).

% remove_var_name(VN,V,VN_)
%   VN is a list of variables
%   V is a variable
%   removes first occurrence of V in VN
%   returns VN_
%   setlog:remove_var/3 can't be used because
%   it removes all ocurrencies of V
%
remove_var_single([], _, []).
remove_var_single([Head| Tail], Element, Remaining) :-
    (   Head == Element ->
        Remaining = Tail
    ;   Remaining = [Head| Tail2],
        remove_var_single(Tail, Element, Tail2)
    ).



%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%                                                %
%                                                %
%                 VC generation                  %
%                                                %
%                                                %
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% if the program for which VC's are being
% generated is called p.pl, then the VC's are
% saved in a file called p-vc.pl
%
% the structure of this file is the following
% - a preamble containing two commented lines
%   with information for the user, a consult
%   command consulting the program for which these
%   VC's were generated and a fact setting the
%   timeout used to run invariance lemmas  --> vc_preamble/2
%
% - a predicate for each VC --> generate_vc/2 and generate_vc/4
%
% - an epilogue (vc_epilogue/2) consisting of:
%   * five predicates that are used to run the
%     VC's and then to pretty-print the result of
%     executing each VC. These predicates are:
%     check_sat_vc, check_unsat_vc, write_ok
%     write_to and write_err
%
%   * a predicate called check_vcs_<program_name>
%     that executes each and every VC one after
%     the other

vc_preamble(FS,FsVC) :-
  FsVC = [[_,FVC],[FAll,_]|_],
  format(FVC,"% Verification conditions for ~s~n~n",FS),
  get_script_name(FS,SN),
  format(FVC,"% Run ~s to see if the program verifies all the VCs~n~n",SN),
  format(FVC,":- notype_check.~n~n",[]),
  format(FVC,":- consult('~s').~n~n",FS),
  print_consult_vc_file(FVC,FAll),
  format(FVC,"% Change this number for a different timeout (ms)\n",[]),
  format(FVC,"def_to(60000).\n\n",[]),
  format(FVC,":- prolog_call(nb_setval(vc_num,0)).~n",[]),
  format(FVC,":- prolog_call(nb_setval(vc_ok,0)).~n",[]),
  format(FVC,":- prolog_call(nb_setval(vc_err,0)).~n",[]),
  format(FVC,":- prolog_call(nb_setval(vc_to,0)).~n",[]),
  format(FVC,":- prolog_call(nb_setval(vc_time,0)).~n~n",[]),
% unsat_sol(Type,ID,,AI,Cons,VN)
%     Type states whether the vc is was generated due
%     to an axiom or an invariant, ID is the name of a
%     VC, AI is the name of the axiom or invariant
%     involved in the vc, Cons is the constraint list
%     returned by {log} and VN are the variable names
%     as in read_term
  format(FVC,":- prolog_call(dynamic(unsat_sol/5)).~n",[]),
% vc_proved(VC) --> VC is a vc already proved
% TODO: put this facts in a file so it can be
%       saved after closing a session
  format(FVC,":- prolog_call(dynamic(vc_proved/1)).~n~n",[]).


print_consult_vc_file(FVC,FAll) :-
write(FVC,{|string(FAll)||
  | :- prolog_call((
  |     retractall(all_unsat_vc(_,_,_,_,_,_)),
  |     retractall(dinvariant(_,_,_)),
  |     retractall(daxiom(_,_,_)),
  |     (exists_file('{FAll}') ->
  |        open('{FAll}',read,StreamVC)
  |     ;
  |        print_notfile('{FAll}')
  |     ),
  |     style_check(-singleton),
  |     setlog:consult_vc(StreamVC),
  |     style_check(+singleton),
  |     close(StreamVC))).
  |
  |}
).

%
% the conjunction of all axioms is satisfiable
%
generate_vc(axioms_sat,Files) :-
  Files = [[_,File]|_],
  (daxiom(AX,Axiom,VNAx) ->
     assertz(vc_sat(axioms_sat)),              % save the id of this VC
     b_getval(tab,Tab),
     write(File,"axioms_sat :-\n"),
     term_string(Axiom,SAxiom,[variable_names(VNAx)]),
     format(File,"~s~s",[Tab,SAxiom]),
     forall((daxiom(AX1,Axiom1,VNAx1),AX1 \== AX),
       (term_string(Axiom1,SAxiom1,[variable_names(VNAx1)]),
        format(File," &~n~s~s",[Tab,SAxiom1])
       )
     ),
     write(File,".\n\n")
  ;
     true
  ).


%
% see generate_vc_wd for documentation
%
generate_vc(axiom_wd,File,Ax,VN) :-
  generate_vc_wd(ax,File,Ax,VN).


%
% see generate_vc_wd for documentation
%
generate_vc(inv_wd,File,Inv,VN) :-
  generate_vc_wd(inv,File,Inv,VN).


%
% each invariant is satisfiable
%
% special case when no initial state is defined
% invariants are satisfiable
%
generate_vc(inv_sat,Files,_,_) :-
  Files = [[_,File]|_],
  b_getval(tab,Tab),
  forall(dinvariant(I,Inv,VNInv),
    (string_concat(I,"_is_sat",H2),
     assertz(vc_sat(H2)),              % save the id of this VC
     format(File,"~s :-~n",H2),
     term_string(Inv,SInv,[variable_names(VNInv)]),
     format(File,"~s~s.~n~n",[Tab,SInv])
   )
  ).
%
% general case
% invariants satisfy initial state
%
generate_vc(inv_sat_ini,Files,Ini,VN) :-
  Files = [[_,File]|_],
  b_getval(tab,Tab),
  Ini =.. [IN | _],
  term_string(Ini,SIni,[variable_names(VN)]),
  string_concat(IN,"_sat_",H1),
  forall(dinvariant(I,Inv,VNInv),
    (string_concat(H1,I,H2),
     assertz(vc_sat(H2)),              % save the id of this VC
     format(File,"~s :-~n",H2),
     term_string(Inv,SInv,[variable_names(VNInv)]),
     format(File,"~s~s &~n",[Tab,SIni]),
     format(File,"~s~s.~n~n",[Tab,SInv])
   )
  ).
%
% Oper is satisfiable and preserves each invariant
%
generate_vc(operation,File,Oper,VN) :-
  oper_is_sat(File,Oper,VN),
  oper_pi_inv(File,Oper,VN).
%
% theorems actually are such
%
generate_vc(theorem,Files,Thrm,VN) :-
  Files = [_,[_,VCFile]|_],
  Thrm =.. [Th | _],
  term_string(Thrm,SThrm,[variable_names(VN)]),
  forall(dtheorem(Th,Thrm,_),
    (assertz(vc_unsat(SThrm,thrm,Th,SThrm,Thrm,VN)),   % save the id of this VC
     format(VCFile,
            "all_unsat_vc(~s,~s,~s,~s,~s).~n",[Th,thrm,Th,SThrm,SThrm])
    )
  ).


%
% the second argument of applyTo, appearing in 
% the fourth argument of foreach predicates,
% belongs to the domain of the first argument
%
% this VC allows to disable the preconditions
% ensuring the consistency of functional 
% predicates
%
% inv_wd stands for invariant is well-defined
%
% Type indicates whether the vc is generated
% due to an axiom or an invariant
%
% TODO: 
%   - this VC should also be generated for
%     foreach and ris appearing in invariants
%     and operations, and for div and apply
%     constraints (if functional predicates 
%     preconditions are going to be disabled)
%   - the invariant is assumed to be stated
%     in a single clause
%   - the invariant is assumed to be a
%     conjunction of atomic predicates
%   - the invariant is assumed to contain at
%     most one foreach (nested or not)
%   - the second argument of applyTo is assumed
%     to be the quantified variable
%   - the quantification domain is assumed to
%     be a subset of the domain of the first
%     argument of applyTo (that is, the 
%     predicate of the foreach isn't expected
%     to further constrain the quantification
%     domain as per the domain of the function)
%
generate_vc_wd(Type,File,P,VN) :-
  setlog:isetlog(P :- Body,usr),!,
  get_applyTo(Body,ApplyTo,Body1),
  forall(nth1(I,ApplyTo,VC), generate_vc_wd1(Type,File,P,VN,I,Body1,VC)).


% Invariant or axiom is well-defined
%
% Pred isn't used but it should
%
generate_vc_wd1(Type,Files,P,VN,I,Body,[X1 in D,Pred,applyTo(F,X2,_),FPred]) :-
  Files = [[_,File],[_,VCFile]|_],
  P =.. [H | _],
  b_getval(tab,Tab),
  string_concat(H,"_is_wd_",H2),
  string_concat(H2,I,H3),
  term_string(P,SP,[variable_names(VN)]),
  split_string(SP,"(","",[_,PVars]),
  string_concat(H3,"(",H4),
  string_concat(H4,PVars,H5),
  assertz(vc_unsat(H3,Type,H,H5,P,VN)),
  format(VCFile,"all_unsat_vc(~s,~s,~s,~s,~s).~n",[H3,Type,H,H5,SP]),
  format(File,"~s :-~n",H5),
  format(File,
         "~s% here conjoin other ax/inv as hypothesis if necessary~n",
         Tab),
  numbervars(X1,23,_),
  setlog:list_to_conj(FPred1,FPred),
  term_variables(FPred,VFPred1),
  term_variables(Body,VBody),
  var_diff(VFPred1,VBody,Param),
  numbervars(X2,24,_),
  % how numbervars is set should be improved
  % based on the variables of D and F (which
  % can be complex terms)
  ((nonvar(D),! ; setlog:get_var(VN,D,_)) -> true ; numbervars(D,3,_)),
  ((nonvar(F),! ; setlog:get_var(VN,F,_)) -> true ; numbervars(F,5,_)),
  term_string(Body,SBody,[variable_names(VN),numbervars(true)]),
  string_concat(SBody1,"true",SBody),
  (SBody1 \== "" ->
     replace_str("&"," & ",SBody1,NBodyt),
     format(File,"~s~s\n",[Tab,NBodyt])
  ;  true
  ),
  format(File,"~sneg(\n",Tab),
  format(File,"~s~sforeach(\n",[Tab,Tab]),
  term_string(X1 in D,SVC1,[variable_names(VN),numbervars(true)]),
  format(File,"~s~s~s~s,\n",[Tab,Tab,Tab,SVC1]),
  term_string(Param,SParam,[variable_names(VN),numbervars(true)]),
  format(File,"~s~s~s~s,\n",[Tab,Tab,Tab,SParam]),
% Pred isn't used but it should
  term_string(Pred,_,[variable_names(VN)]),
%  format(File,"~s~s~s~s\n",[Tab,Tab,Tab,SVC2]),
  term_string(ncomp({[X2,X2]},F,{}),SVC3,[variable_names(VN),numbervars(true)]),
  format(File,"~s~s~s~s,\n",[Tab,Tab,Tab,SVC3]),
% if Pred is used substitute the above line by this one:
%  format(File,"~s~s~simplies ~s\n",[Tab,Tab,Tab,SVC3]),
  term_string(FPred1,SFPred,[variable_names(VN),numbervars(true)]),
  (SFPred == "true" -> 
     SFPred1 = SFPred ; string_concat(SFPred1,"&true",SFPred)),
  replace_str("&"," & ",SFPred1,SFPred2),
  format(File,"~s~s~s~s\n",[Tab,Tab,Tab,SFPred2]),
  format(File,"~s~s)\n",[Tab,Tab]),
  format(File,"~s).\n\n",Tab).

  
% Operation is satisfiable
%
% if oper(A,B,A,B) then print(oper(A,B,A,B))
% if oper(A,B,A_,B) then print(oper(A,B,A_,B) & A neq A_)
% if oper(A,B,A_,B_) then print(oper(A,B,A_,B_) & [A,B] neq [A_,B_])
%
oper_is_sat(Files,Oper,VN) :-
  Files = [[_,File]|_],
  b_getval(tab,Tab),
  Oper =.. [ON | Vars],
  string_concat(ON,"_is_sat",H1),
  assertz(vc_sat(H1)),              % save the id of this VC
  format(File,"~s :-\n",H1),
  term_string(Oper,SOper,[variable_names(VN)]),
  get_before_next_vars(VN,Vars,BVars,NVars),
  (BVars == [] ->
     format(File,"~s~s.~n~n",[Tab,SOper])
  ;
   BVars = [BV] ->
     NVars = [NV],
     format(File,"~s~s & ~n",[Tab,SOper]),
     format(File,"~s~s neq ~s.~n~n",[Tab,BV,NV])
  ;
     atomics_to_string(BVars,",",SBVars),
     atomics_to_string(NVars,",",SNVars),
     format(File,"~s~s & ~n",[Tab,SOper]),
     format(File,"~sdelay([~s] neq [~s],false).~n~n",[Tab,SBVars,SNVars])
  ).


% Operation preserves each invariant
%
oper_pi_inv(Files,Oper,VN) :-
  Files = [[_,File],[_,VCFile]|_],
  b_getval(tab,Tab),
  Oper =.. [ON | Vars],
  get_before_next_vars(VN,Vars,BVars,_),
  string_concat(ON,"_pi_",H1),
  string_concat(Tab,Tab,TT),
  term_string(Oper,SOper,[variable_names(VN)]),
  forall(dinvariant(I,Inv,VNInv),
  %
  % add "_" to each variable V in Inv if V_ is in Oper
  % otherwise leave V unchanged
  % in this way variables not modified by Oper remain
  % the same in Inv
  % Example: inv(A,B) & oper(A,B,A_,B) implies inv(A_,B)
  %
    (string_concat(H1,I,H2),
     split_string(SOper,"(","",[_,OpVars]),
     Inv =.. [_|IVars],
     term_string(IVars,SIV1,[variable_names(VNInv)]),
     string_concat("[",SIV2,SIV1),
     string_concat(SInv,"]",SIV2),
     string_concat(H2,"(",H31),
     string_concat(H31,SInv,H32),
     string_concat(H32,",",H3),
     string_concat(H3,OpVars,H4),
     add_varnames(VNInv,VN,VN1),
     assertz(vc_unsat(H2,inv,I,H4,Oper,VN1)),          % save the id of this VC
     format(VCFile,"all_unsat_vc(~s,~s,~s,~s,~s).~n",[H2,inv,I,H4,SOper]),
     %
     % SInv is a string containing the variables in Inv
     % add the prime character to the variables in SInv \cap BVars
     % save the result in SInv_ in the form of a string
     %
     split_string(SInv,",","",LIVars),
     add_prime_char(BVars,LIVars,LPVI),
     atomics_to_string(LPVI,",",SInv_),
     %
     % if SInv_ is different from SInv (i.e., at least one of the
     % variables in SInv was decorated with "_"), then generate
     % the corresponding invariance lemma; otherwise generate
     % "true" because the operation doesn't change any of Inv's
     % variables
     %
     (SInv_ \== SInv ->
        format(File,"~s :-~n",H4),
        format(File,
               "~s% here conjoin other ax/inv as hypothesis if necessary~n",
               Tab),
        format(File,"~sneg(~n",Tab),
        format(File,"~s~s(~s) &~n",[TT,I,SInv]),
        format(File,"~s~s implies~n",[TT,SOper]),
        format(File,"~s~s(~s)~n",[TT,I,SInv_]),
        format(File,"~s).~n~n",Tab)
     ;
        format(File,"~s:-~n",H4),
        format(File,"~s% ~s doesn't change ~s variables~n",[Tab,ON,I]),
        format(File,"~sneg(true).~n~n",Tab)
     )
    )
  ).


vc_epilogue(FS,FVCS) :-
  FVCS = [[_,FVC]|_],
  b_getval(tab,Tab),
  print_update_time(FVC),
  print_update_count(FVC),
  print_check_sat_vc(FVC),
  print_check_unsat_vc(FVC),
  print_write_ok(FVC,Tab),
  print_write_to(FVC,Tab),
  print_write_err(FVC,Tab),
  print_script(FS,FVC),
  print_script_aux(FVC),
  print_sat_vcs(FVC,Tab),
  print_unsat_vcs(FVC,Tab),
  print_stats(FVC),
%  format(FVC,"~strue.~n~n",Tab),
  print_directive(FS,FVC).

print_update_time(FVC) :-
write(FVC,{|string||
  | update_time(Tf,Ti) :-
  |   prolog_call(
  |     (nb_getval(vc_time,VCT),
  |      VCT_ is VCT + Tf - Ti,
  |      nb_setval(vc_time,VCT_)
  |     )
  |   ).
  |
  |}
).

print_update_count(FVC) :-
write(FVC,{|string||
  | update_count(C) :-
  |   prolog_call(
  |     (nb_getval(C,VCN),
  |      VCN_ is VCN + 1,
  |      nb_setval(C,VCN_)
  |     )
  |   ).
  |
  |}
).

print_check_sat_vc(FVC) :-
write(FVC,{|string||
  | check_sat_vc(VCID) :-
  |   prolog_call((setlog:vc_proved(VCID) -> R = proved ; R = unproved)) &
  |   (R == unproved &
  |    write('\nChecking ') & write(VCID) & write(' ... ') &
  |    update_count(vc_num) &
  |    ((prolog_call(setlog(VCID)) &
  |     update_count(vc_ok) &
  |     prolog_call(assertz(vc_proved(VCID))) &
  |     write_ok)!
  |     or
  |     update_count(vc_err) &
  |     write_err
  |    )
  |    or
  |    R == proved
  |   ).
  |
  |}
).

print_check_unsat_vc(FVC) :-
write(FVC,{|string||
  | check_unsat_vc(VCID) :-
  |   def_to(TO) &
  |   prolog_call(
  |     (VCID =.. [H | _],
  |      (\+setlog:vc_proved(H) ->
  |         setlog:all_unsat_vc(H,T,ID,VC,Op,VN),
  |         write('\nChecking '), write(H), write(' ... '), flush_output,
  |         setlog(update_count(vc_num)),
  |         get_time(Ti),
  |         rsetlog(VC,TO,Cons,Res,[]),
  |         get_time(Tf)
  |      ;
  |         Res = proved
  |      )
  |     )
  |   ) &
  |   ((Res = failure)! &
  |     update_count(vc_ok) &
  |     update_time(Tf,Ti) &
  |     prolog_call((retractall(setlog:unsat_sol(_,H,_,_,_)),
  |                  assertz(vc_proved(H)))) &
  |     write_ok
  |   or
  |    (Res = timeout)! &
  |     update_count(vc_to) &
  |     write_to
  |   or
  |     (Res = proved)!
  |   or
  |     update_count(vc_err) &
  |     % saves the solution to be used by findh
  |     prolog_call((retractall(setlog:unsat_sol(_,H,_,_,_)),
  |                  assertz(unsat_sol(T,H,ID,Cons,VN)))) &
  |     write_err
  |   ).
  |
  |}
).

print_write_ok(FVC,Tab) :-
  write(FVC,"write_ok :-\n"),
  format(FVC,"~sprolog_call(ansi_format([bold,fg(green)],'OK',[])).\n\n",Tab).

print_write_to(FVC,Tab) :-
  write(FVC,"write_to :-\n"),
  format(FVC,"~sprolog_call(ansi_format([bold,fg(255,255,50)],'TIMEOUT',[])).\n\n",Tab).

print_write_err(FVC,Tab) :-
  write(FVC,"write_err :-\n"),
  format(FVC,"~sprolog_call(ansi_format([bold,fg(red)],'ERROR',[])).\n\n",Tab).

print_directive(FS,FVC) :-
  get_script_name(FS,SN),
  format(FVC,":- nl & prolog_call(ansi_format([bold,fg(green)],'Type checking has been deactivated.',[])) & nl & nl.~n~n",[]),
  format(FVC,":- nl & prolog_call(ansi_format([bold,fg(green)],'Call ~s to run the verification conditions.',[])) & nl & nl.~n~n",SN).

print_script(FS,FVC) :-
  get_script_name(FS,SN),
  string_concat(SN," :- prolog_call(setlog(check_aux!)).\n\n",L12),
  write(FVC,L12).

get_script_name(FS,SN) :-
  sub_atom(FS,I,_,_,'.pl'),!,
  sub_atom(FS,0,I,_,File1),
  atom_string(File1,SFS),
  string_concat("check_vcs_",SFS,SN).
get_script_name(FS,SN) :-
  sub_atom(FS,I,_,_,'.slog'),!,
  sub_atom(FS,0,I,_,File1),
  atom_string(File1,SFS),
  string_concat("check_vcs_",SFS,SN).

print_script_aux(FVC) :-
indent_lines("",{|string||
  |check_aux :-
  |  prolog_call(
  |    (retractall(unsat_sol(_,_,_,_,_)),
  |     nb_setval(vc_num,0),
  |     nb_setval(vc_time,0),
  |     nb_setval(vc_ok,0),
  |     nb_setval(vc_err,0),
  |     nb_setval(vc_to,0)
  |    )
  |  ) &
  |},S),
write(FVC,S).


print_sat_vcs(FVC,Tab) :-
  forall(vc_sat(ID),format(FVC,"~scheck_sat_vc(~s) &~n",[Tab,ID])).

print_unsat_vcs(FVC,Tab) :-
  forall(vc_unsat(_,_,_,L,_,_),format(FVC,"~scheck_unsat_vc(~s) &~n",[Tab,L])).

print_stats(FVC) :-
indent_lines("  ",{|string||
  |  prolog_call(
  |    (nb_getval(vc_num,VCN),
  |     nb_getval(vc_time,VCT),
  |     nb_getval(vc_ok,VCOK),
  |     nb_getval(vc_err,VCE),
  |     nb_getval(vc_to,VCTO)
  |    )
  |  ) &
  |  nl & nl &
  |  write("Total VCs: ") & write(VCN) &
  |  write(" (discharged: ") & write(VCOK) &
  |  write(", failed: ") & write(VCE) &
  |  write(", timeout: ") & write(VCTO) & write(")") & nl &
  |  write("Execution time (discharged): ") & write(VCT) & write(" s").
  |
  |},S),
write(FVC,S).



% get_before_next_vars(VN,Vars,BVars,NVars)
% Vars is a list of variables
% if in Vars there is a primed variable then put
% the base name in BVars and the full name in NVars
get_before_next_vars(VN,Vars,BVars,NVars) :-
  term_string(Vars,SVars,[variable_names(VN)]),
  string_concat("[",SV1,SVars),
  string_concat(SV2,"]",SV1),
  split_string(SV2,",","",SSVars),
  get_primed_vars(SSVars,BVars,NVars).

get_primed_vars([],[],[]) :- !. 
get_primed_vars([P|L],BV,NV) :-
  string_concat(P_,"_",P),!,
  get_primed_vars(L,BV1,NV1),
  BV = [P_|BV1],
  NV = [P |NV1].
get_primed_vars([_|L],BV,NV) :-
  get_primed_vars(L,BV,NV).
  
% add_prime_char(PVars,L,L_)
add_prime_char(_,[],[]) :- !.
add_prime_char(PVars,[P|L],LP) :-
  (member(P,PVars) -> string_concat(P,"_",P1) ; P1 = P),
  add_prime_char(PVars,L,LP1),
  LP = [P1 | LP1].

% get_applyTo(Body,ApplyTo,NBody)
% Body is a conjunction of {log} predicates
% ApplyTo is a list of 4-tuples 
% [Dom,Pred,applyTo(F,X,Y),FPred]
% NBody is Body minus foreach, set, rel, integer
% get_applyTo searches for applyTo constraints
% appearing in the fourth argument of foreach
% constraints. For each such constraint it puts
% in ApplyTo a 4-tuple where Dom is the 
% quantification domain of the foreach
% containing the applyTo, Pred is the predicate
% of the foreach, applyTo(F,X,Y) is the applyTo
% constraint and FPred is the functional
% predicate of the foreach without applyTo's
get_applyTo(Body,ApplyTo,NBody) :-
  get_applyTo1(Body,ApplyTo1,NBody),
  make_4_tuples(ApplyTo1,ApplyTo2),
  simp_and_reduce(ApplyTo2,ApplyTo).

get_applyTo1((C & F),ApplyTo,Body) :-
  C = foreach(_,_,_,_),!,
  get_applyTo_foreach(C,ApplyTo1),
  get_applyTo1(F,ApplyTo11,Body),
  append(ApplyTo1,ApplyTo11,ApplyTo).
get_applyTo1((C & F),ApplyTo,Body) :-
  C =.. [H | _],
  member(H,[set,rel,integer,dec]),!,  % these constraints aren't passed to Body
  get_applyTo1(F,ApplyTo,Body).  
get_applyTo1((C & F),ApplyTo,Body) :-
  Body = (C & Body1),
  get_applyTo1(F,ApplyTo,Body1),!.
get_applyTo1(C,ApplyTo,true) :-
  C = foreach(_,_,_,_),!,
  get_applyTo_foreach(C,ApplyTo).
%  ApplyTo = [[Dom,Pred,ApplyTo1]].
get_applyTo1(C,[],true) :-
  C =.. [H | _],
  member(H,[set,rel,integer,dec]),!.  % these constraints aren't passed to Body
get_applyTo1(C,[],C).

get_applyTo_foreach(C,ApplyTo) :-
  C = foreach(Dom,_,Pred,FPred),!,
  get_applyTo_foreach1(FPred,ApplyTo1,FPred1),
  get_applyTo_foreach(Pred,ApplyTo11),   % Pred can be a foreach
  add_dom(Dom,ApplyTo11,ApplyTo12),
  ApplyTo = [[Dom,Pred,ApplyTo1,FPred1] | ApplyTo12].
get_applyTo_foreach(_,[]).
  
get_applyTo_foreach1((C & F),ApplyTo,FPred) :-
  C = applyTo(_,_,_),!,
  ApplyTo = [C | ApplyTo1],
  get_applyTo_foreach1(F,ApplyTo1,FPred).
get_applyTo_foreach1((C & F),ApplyTo,FPred) :-
  C =.. [H | _],
  member(H,[dec,rel,set,integer]),!,
  get_applyTo_foreach1(F,ApplyTo,FPred).
% the following clause should be improve as
% to include only the constraints that are
% related to X in applyTo(F,X,Y)
get_applyTo_foreach1((C & F),ApplyTo,FPred) :-
  !,
  FPred = [C | FPred1],
  get_applyTo_foreach1(F,ApplyTo,FPred1).
get_applyTo_foreach1(applyTo(F,X,Y),[applyTo(F,X,Y)],[]) :- !.
get_applyTo_foreach1(true,[],[]) :- !.
get_applyTo_foreach1(C,[],[C]).

add_dom(_,[],[]) :- !.
add_dom(Dom,[[D,P,A,FP]|L],[[[Dom,D],P,A,FP]|L1]) :-
  add_dom(Dom,L,L1).
  
make_4_tuples([],[]) :- !.
make_4_tuples([[Dom,Pred,App,FPred]|ApplyTo1],ApplyTo) :-
  make_4_tuples1(Dom,Pred,App,FPred,App1),
  make_4_tuples(ApplyTo1,ApplyTo11),
  append(App1,ApplyTo11,ApplyTo).

make_4_tuples1(_,_,[],_,[]) :- !.
make_4_tuples1(Dom,Pred,[A|App],FPred,Applies) :-
  make_4_tuples1(Dom,Pred,App,FPred,Applies1),
  Applies = [[Dom,Pred,A,FPred] | Applies1].

% removes 3-tuples when the same function
% is applied to an element of the same
% set (reduce)
% eliminates unnecessary X in Dom
% constraints  (simplify)
simp_and_reduce(ApplyTo,NApplyTo) :-
  simplify(ApplyTo,ApplyTo1),
  reduce(ApplyTo1,NApplyTo).

% (1) check if the variables appearing in the
%     second argument of an applyTo constraint appear
%     also in the control expression
simplify([],[]) :- !.
simplify([[X in D,P,A,FP]|ApplyTo],[[X in D,P,A,FP]|NApplyTo]) :-
  !,
  simplify(ApplyTo,NApplyTo).
simplify([[[X1 in D|_],P,applyTo(F,X2,_),FP]|ApplyTo],NApplyTo) :-
  term_variables(X1,VX1),
  term_variables(X2,VX2),
  forall(member(X,VX2),setlog:member_strong(X,VX1)),!, % (1)
  simplify(ApplyTo,ApplyTo1),
  NApplyTo = [[X1 in D,P,applyTo(F,X2,_),FP]|ApplyTo1].
simplify([[[_ in _|Dom],P,applyTo(F,X2,_),FP]|ApplyTo],NApplyTo) :-
  !,
  simplify([[Dom,P,applyTo(F,X2,_),FP]|ApplyTo],NApplyTo).

reduce([],[]) :- !.
reduce([[X1 in D,P,applyTo(F,X2,_),FP]|ApplyTo],NApplyTo) :-
  !,
  (dup_app(D,F,ApplyTo) ->
     reduce(ApplyTo,NApplyTo)
  ;
     reduce(ApplyTo,NApplyTo1),
     NApplyTo = [[X1 in D,P,applyTo(F,X2,_),FP]|NApplyTo1]
  ).
reduce([A|ApplyTo],[A|NApplyTo]) :-
  reduce(ApplyTo,NApplyTo).

dup_app(D1,F1,[[_ in D2,_,applyTo(F2,_,_),_]|_]) :-
  D1 == D2, F1 == F2,!.
dup_app(D,F,[_|ApplyTo]) :-
  dup_app(D,F,ApplyTo).


replace_str(P,W,S,NS) :-
  sub_string(S,B,_,A,P),!,
  sub_string(S,0,B,_,S1),
  sub_string(S,_,A,0,S2),
  replace_str(P,W,S2,NS2),
  string_concat(S1,W,SS),
  string_concat(SS,NS2,NS)
  ;
  NS = S.


var_diff([],_,[]) :- !.
var_diff(A,[],A) :- !.
var_diff([X|A],B,C) :-
  (setlog:member_strong(X,B) ->
     var_diff(A,B,C)
  ;
     var_diff(A,B,C1),
     C = [X | C1]
  ).


add_varnames([],VN2,VN2) :- !.
add_varnames([X = Y | VN1],VN2,VN3) :-
  (member(X = _,VN2) ->
     add_varnames(VN1,VN2,VN3)
  ;
     VN3 = [X = Y | VN31],
     add_varnames(VN1,VN2,VN31)
  ).


consult_vc(F) :-
  read_clause(F,Clause,[variable_names(VN)]),
    (Clause \== end_of_file ->
       Clause =.. [H|P],
       append(P,[VN],P1),
       (H == all_unsat_vc,!,
          P1 = [A1,B1,C1,D1,E1,F1], assertz(all_unsat_vc(A1,B1,C1,D1,E1,F1))
       ;
        H == dinvariant,
          P1 = [A1,B1,C1], assertz(dinvariant(A1,B1,C1))
       ;
        H == daxiom,
          P1 = [A1,B1,C1], assertz(daxiom(A1,B1,C1))
       ),
       consult_vc(F)
    ; true
    ).



% setlog_findh-1.0

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%                                                %
%                                                %
%                Hypothesis finder               %
%                                                %
%   for {log} programs modeling state machines   %
%                                                %
%                                                %
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%


%
% These prredicats retrieve the solutions saved by
% VCG, when an unsatisfiability vc couldn't be
% proved, and iterates over axioms and/or
% invariants to see if any of the solutions
% is a solution of the axiom or invariant.
% That is if S is one of the retrieved solutions
% and P is an axiom or invariant, {log} is called
% on S & P. If the answer is false, then P is a
% missed hypothesis of the vc corresponding to S.
% This is so because if the vc was VC and it
% returned S, then P & VC won't return S because
% S & P has been proved to be false.
%
% The user interface are the following commands
%   -findh/0: prints the missing hypothesis for
%    all the failed vc's. It tries one axiom or
%    invariant at a time. For some vc's this
%    may not be enough as sometimes two or more
%    axioms or invariants are needed to prove a
%    vc. See findhn/0.
%
%  -findh/1: prints the missing hypothesis for
%   the vc passed as an argument. Works as
%   findh/0.
%
% These predicates work over the *-vc file
% consulted and whose check_vcs_* command has
% just been executed.
%
% TODO
%
% Provide support for theorems. The problem is
% that we don't have the position of the
% theorem and so we don't know the list of the
% previous ax/inv that can be used as hypothesis
%
% user commands

setlog_command(findh) :- !.    
setlog_command(findh(_)) :- !.    
setlog_command(findh(_,_,_,_)) :- !.
setlog_command(findhn(_)) :- !.    
setlog_command(findhn(_,_)) :- !.    

ssolve_command(findh) :- !,     
    findh.
ssolve_command(findh(VC)) :- !,     
    findh(VC).
ssolve_command(findh(VC,N,EO,OnlyExclude)) :- !,     
    findh(VC,N,EO,OnlyExclude).
ssolve_command(findhn(N)) :- !,       
    findhn(N).
ssolve_command(findhn(VC,N)) :- !,  
    findhn(VC,N).      

% findh(vc,n,o|e,axinv)
% vc is the name of the vc for which the user
% wants to find missed hypothesis
% n is the number of axioms or invariants
% to be tried at a time
% o|e o:only, e:exclude
% axinv list of axioms or invariants
% o uses only axioms or invariants in axinv
% e excludes axinv from the list of available
% axioms and invariants
findh(VC,N,EO,OnlyExclude) :-
  nonvar(VC),
  integer(N),
  ground(OnlyExclude),
  (setlog:unsat_sol(T,VC,AI,Cons,VN) ->
     findh(N,VC,EO,OnlyExclude,T,VC,AI,Cons,VN)   % findh/9
  ;
     print_no_sol(VC)
  ).

%
% findh
% prints the missing hypothesis for all the
% failed vc's. 
% tries N ax/inv at a time for
% N in int(1,number_ax_inv) until one
% hypothesis is found
%
findh :-
  (setlog:unsat_sol(_,_,_,_,_) ->
     forall(setlog:unsat_sol(T,VC,AI,Cons,VN),findh(VC,T,VC,AI,Cons,VN)) % /6
  ;
     print_no_unproved_vc
  ).

% findhn(N) tries N axioms or invariants at a time.
findhn(N) :-
  integer(N),
  (setlog:unsat_sol(_,_,_,_,_) ->
     forall(setlog:unsat_sol(T,VC,AI,Cons,VN),findh(N,VC,T,VC,AI,Cons,VN)) % /7
  ;
     print_no_unproved_vc
  ).


% findh(VC)
% VC is the name of the vc for which the user
% wants to find missed hypothesis
% prints the missing hypothesis of VC
% tries N ax/inv at a time for
% N in int(1,number_ax_inv) until one
% hypothesis is found
%
findh(VC) :-
  nonvar(VC),
  (setlog:unsat_sol(T,VC,AI,Cons,VN) ->
     findh(VC,T,VC,AI,Cons,VN)   % findh/6
  ;
     print_no_sol(VC)
  ).

% findhn(VC,N) tries N axioms or invariants at a time.
findhn(VC,N) :-
  nonvar(VC),
  integer(N),
  (setlog:unsat_sol(T,VC,AI,Cons,VN) ->
     findh(N,VC,T,VC,AI,Cons,VN)   % findh/7
  ;
     print_no_sol(VC)
  ).


% findh/6
% findh(VC,T,VC,AI,Cons,VN)
% VC is the name of the vc for which the user
% wants to find missed hypothesis
%
findh(VC,T,VC,AI,Cons,VN) :-
  write('Missing hypotheses for '),
  write(VC), write(': '),
  (T == thrm ->
     write('use findh/4 for theorems'),nl
  ;
     findh1(T,AI,Cons,VN,MH),    % findh1/5
     write(MH),nl
  ).

% findh/7
findh(N,VC,T,VC,AI,Cons,VN) :-
  write('Missing hypotheses for '),
  write(VC), write(': '),
  findh1(T,N,AI,Cons,VN,MH),  % findh1/6
  write(MH),nl.

% findh/9
findh(N,VC,o,Only,T,VC,AI,Cons,VN) :-
  write('Missing hypotheses for '),
  write(VC), write(': '),
  (T == thrm ->
     write('use findh/4 for theorems'),nl
  ;
     findh1(T,N,o,Only,AI,Cons,VN,MH),  % findh1/8
     write(MH),nl
  ).
  
% findh/9
findh(N,VC,e,Exclude,T,VC,AI,Cons,VN) :-
  write('Missing hypotheses for '),
  write(VC), write(': '),
  findh1(T,N,e,Exclude,AI,Cons,VN,MH),  % findh1/8
  write(MH),nl.
  

% findh1/5
findh1(inv,AI,Cons,VN,MH) :-
  all_hyph(ax,ID,AllAx),
  all_hyph(inv,ID,AllInv),
  append(AllAx,AllInv,All),
  length(All,N),
  findh1(1,N,All,AI,Cons,VN,MH).  % findh1/7

findh1(ax,AI,Cons,VN,MH) :-
  all_hyph(ax,AI,All),
  length(All,N),
  findh1(1,N,All,AI,Cons,VN,MH).  % findh1/7

% theorems can use as hypothesis only
% the ax/inv before them. this ordering
% doesn't exists in VCG.
% as a (possible inconsistent) workaround
% theorems are treated as invariants
findh1(thrm,AI,Cons,VN,MH) :-
  findh1(inv,AI,Cons,VN,MH).

% findh1/6
findh1(inv,N,ID,Cons,VN,MH) :-
  all_hyph(ax,ID,AllAx),
  all_hyph(inv,ID,AllInv),
  append(AllAx,AllInv,All),
  findh2(N,All,Cons,VN,MH).

findh1(ax,N,AI,Cons,VN,MH) :-
  all_hyph(ax,AI,All),
  findh2(N,All,Cons,VN,MH).

findh1(thrm,N,AI,Cons,VN,MH) :-
  findh1(inv,N,AI,Cons,VN,MH).

% findh1/7
% while K =< N & not(findh2(K,All,AI,Cons,VN,MH)) do {I := I + 1}
% in first call K = 1
findh1(K,N,All,AI,Cons,VN,MH) :-
  findh2(K,All,Cons,VN,MH),   % findh2/5
  (MH == [] ->
     (K < N -> J is K + 1, findh1(J,N,All,AI,Cons,VN,MH) ; true)
  ;
     true
  ).


% findh1/8
% searching hypothesis for theorems is 
% supported only if the user provides
% the list of possible hypothesis because
% otherwise we don't know the list of 
% previous ax/inv
findh1(thrm,N,OE,Only,ID,Cons,VN,MH) :-
  findh1(inv,N,OE,Only,ID,Cons,VN,MH).

% searches only ax/inv in Only
findh1(inv,N,o,Only,ID,Cons,VN,MH) :-
  all_hyph(ax,o,ID,Only,AllAx),
  all_hyph(inv,o,ID,Only,AllInv),
  append(AllAx,AllInv,All),
  findh2(N,All,Cons,VN,MH).

% findh1/8
% doesn't search ax/inv in Exclude
findh1(inv,N,e,Exclude,ID,Cons,VN,MH) :-
  all_hyph(ax,e,ID,Exclude,AllAx),
  all_hyph(inv,e,ID,Exclude,AllInv),
  append(AllAx,AllInv,All),
  findh2(N,All,Cons,VN,MH).

% findh1/8
% searches only ax in Only
findh1(ax,N,o,Only,ID,Cons,VN,MH) :-
  all_hyph(ax,o,ID,Only,All),
  findh2(N,All,Cons,VN,MH).

% findh1/8
% doesn't search ax in Exclude
findh1(ax,N,e,Exclude,ID,Cons,VN,MH) :-
  all_hyph(ax,e,ID,Exclude,All),
  findh2(N,All,Cons,VN,MH).


% findh2/5
findh2(N,All,Cons,VN,MH) :-
  findall(ID,
          (comb(N,All,Comb),
           mk_id_frm_vn(Comb,ID,Frm,VNFrm),
           is_missing(Cons,VN,Frm,VNFrm)
          ),
          MH
  ).


is_missing(Cons,VNCons,P,VNP) :-
  generate_eq(VNCons,VNP,Eq1),
  % the next call generates many redundant equalities
  generate_eq(VNP,VNP,Eq2),
  append(Eq1,Eq2,Eq),
  append(Eq,Cons,L1),
  append(P,L1,L),
  setlog:list_to_conj(F,L),
  \+setlog(F,5000,_,_,[]).


% generate_eq(VN,VNP,Eq)
generate_eq([],_,[]) :- !.
generate_eq([X = Y | VN],VNP,Eq) :-
  get_all_vars(X,VNP,Vars),           % in VNP the same variable name (X) can
  (Vars \== [] ->                     % appear many times (see mk_id_frm_vn)
     maplist(mk_eq(Y),Vars,VarsEq),
     append(VarsEq,Eq1,Eq),
     generate_eq(VN,VNP,Eq1)
  ;
     generate_eq(VN,VNP,Eq)
  ).


solution(VC) :-
  (setlog:unsat_sol(_,VC,_,Cons,VN) ->
     print_vars(VN,VN),nl,
     write('Constraints: '),
     print_cons(Cons,VN),nl
  ;
     print_no_sol(VC)
  ).

print_vars([],_) :- !.
print_vars([X = Y | Vars],VN) :-
  (var(Y) ->
     (setlog:get_var(Vars,Y,V) -> write(X = V),nl ; true)
  ;
     term_string(Y,SY,[variable_names(VN)]),
     write(X),write(' = '),write(SY),nl
  ),
  print_vars(Vars,VN).


print_cons([],_) :- !.
print_cons([C],_) :-
  C =.. [H|_],
  member(H,[set,integer,rel]),
  !.
print_cons([C],VN) :- !,
  term_string(C,SC,[variable_names(VN)]),
  write(SC).
print_cons([C | Cons],VN) :-
  C =.. [H|_],
  member(H,[set,integer,rel]),
  print_cons(Cons,VN).
print_cons([C | Cons],VN) :-
  term_string(C,SC,[variable_names(VN)]),
  write(SC),write(' & '),
  print_cons(Cons,VN).


all_hyph(ax,I,All) :-
  all_hyph(ax,e,I,[],All).

all_hyph(inv,I,All) :-
  all_hyph(inv,e,I,[],All).

all_hyph(ax,o,I,Only,All) :-
  findall([ID,Ax,VNAx],
    (setlog:daxiom(ID,Ax,VNAx),ID \== I, member(ID,Only)),
    All).

all_hyph(inv,o,I,Only,All) :-
  findall([ID,Inv,VNInv],
    (setlog:dinvariant(ID,Inv,VNInv),ID \== I, member(ID,Only)),
    All).

all_hyph(ax,e,I,Exclude,All) :-
  findall([ID,Ax,VNAx],
    (setlog:daxiom(ID,Ax,VNAx),ID \== I, \+member(ID,Exclude)),
    All).

all_hyph(inv,e,I,Exclude,All) :-
  findall([ID,Inv,VNInv],
    (setlog:dinvariant(ID,Inv,VNInv),ID \== I,\+member(ID,Exclude)),
    All).


mk_id_frm_vn([],[],[],[]) :- !.
mk_id_frm_vn([[I,P,V]|PW],ID,Frm,VNFrm) :-
  ID = [I | ID1],
  Frm = [P | Frm1],
  append(V,VNFrm1,VNFrm),
  mk_id_frm_vn(PW,ID1,Frm1,VNFrm1).


get_all_vars(_,[],[]) :- !.
get_all_vars(X,[Y = Z| VN],Vars) :-
  X == Y,!,
  Vars = [Z|Vars1],
  get_all_vars(X,VN,Vars1).
get_all_vars(X,[_| VN],Vars) :-
  get_all_vars(X,VN,Vars).

% to be used by maplist
mk_eq(X,Y,X=Y).


% taken from http://kti.ms.mff.cuni.cz/~bartak/prolog/combinatorics.html
comb(0,_,[]).
comb(N,[X|T],[X|Comb]):-N>0,N1 is N-1,comb(N1,T,Comb).
comb(N,[_|T],Comb):-N>0,comb(N,T,Comb).


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%                                                 %
%                                                 %
%                  Error printing                 %
%                                                 %
%                                                 %
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

print_wrong_declaration(Dir) :-
  format("vcg error: incorrect ~s declaration~n",Dir).

print_unexpected_clause(Dir,H) :-
  format("vcg error: searching ~s, ~s was found~n",[Dir,H]).

print_not_param(T,V) :-
  format("vcg error: in ~s, ~s is not a parameter~n",[T,V]).

print_only_params_state(T,X) :-
  format("vcg error: in ~s, ~s is not a variable~n",[T,X]).

print_only_vars(T,V) :-
  format("vcg error: in ~s, ~s is not a parameter or state variable~n",[T,V]).

print_no_stateVariable(T) :-
  format("vcg error: ~s doesn't depend on state variables~n",T).

print_wrong_order(Dir) :-
  format("vcg error: ~s declaration is in a wrong place~n",Dir).

print_no_param :-
  write("vcg error: no parameters declared, no axiom can be stated\n").

print_var_param :-
  write("vcg error: a variable is also a parameters\n").

print_dup_var(P) :-
  write("vcg error: duplicate variables in declaration "),
  write(P),
  write("\n").

print_miss_dir(IN,Inv) :-
  Inv =.. [H | _],
  format("vcg error: instead of ~s, ~s was found~n",[IN,H]).

print_dup_dir(Dir) :-
  format("vcg error: ~s is duplicated~n",Dir).

print_state_var_miss(Dir,X) :-
  format(
    "vcg error: in ~s there's variable ~s but not ",[Dir,X]),
  atom_string(X,SX),
  (string_concat(Q,"_",SX) ->
     format("~s~n",Q)
  ;
     format("~s again or ~s_~n",[SX,SX])
  ).

print_not_state_var(Dir,X) :-
  format(
    "vcg error: in ~s variable ~s can't be primed; it's not a state variable~n",
    [Dir,X]).

print_no_operation :-
  write("vcg error: the state machine has no operations"),nl.
  
print_too_many(T,X) :-
  format("vcg error: in ~s variable ~s is repeated too many times ",[T,X]).

print_in_spec(KW,H,A) :-
  (member(KW,[parameters,variables]),!,
   format("vcg error: ~s/1 has more than one clause~n",KW)
   ;
   (member(KW,[axiom,invariant,operation]),!,
    string_concat("an ",KW,KW1)
   ;
    KW == theorem,!,
    string_concat("a ",KW,KW1)
   ;
    % KW == initial
    string_concat("the ",KW,KW2),
    string_concat(KW2," condition",KW1)
   ),
   format(
     "vcg error: ~s/~d is declared as ~s, can't have more than one clause~n",
     [H,A,KW1]
   )
  ).

print_no_sol(VC) :-
  format("findh error: it seems that ~s has been proved~n",VC).

print_no_unproved_vc :-
  format("findh error: it seems there are no unproved vc~n").

print_notfile(File) :-
  format("vcg error: file ~s doesn't exist~n",File).



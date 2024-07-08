%setlog498-15e

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%
%%                The {log} interpreter and solver
%%
%%                           VERSION 4.9.8
%%
%%                      original development by
%%                Agostino Dovier     Eugenio Omodeo
%%                Enrico Pontelli     Gianfranco Rossi
%%
%%                    subsequent enhancements by
%%                         Gianfranco Rossi
%%                    with the contribution of
%%       B.Bazzan  S.Manzoli  S.Monica  C.Piazza  L.Gelsomino
%%
%%                        Last revision by
%%               Gianfranco Rossi and Maximiliano Cristia'
%%                          (May 2024)
%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

:- module(setlog, [
    op(980,xfy,[implies,nimplies]),   
    op(970,xfy,or),
    op(950,xfy,&),
    op(900,fy,[naf,neg,cneg]),
    op(800,xf,!),
    op(700,xfx,[in,neq,nin]),
    %op(650,yfx,[with,mwith]),   
    op(650,yfx,[with]),
    op(400,yfx,\),     
    op(350,xfy,':'),    
    %op(150,fx,*),     %for bags only
    % for interactive use
    setlog/0,
    % to call setlog from Prolog
    setlog/1,
    setlog/2,
    setlog/3,
    setlog/4,
    setlog/5,
    rsetlog/5,
    rsetlog_str/6,
    setlog_str/2,
    setlog_str/3,
    setlog_str/4,
    setlog_str/6,
    setlog_tc/3,
    setlog_consult/1,
    consult_lib/0,
    setlog_clause/1,
    setlog_config/1,
    setlog_rw_rules/0,
    setlog_help/0,
    h/1
]).

:- use_module(library(dialect/sicstus/timeout)).
:- use_module(library(lists), [append/3,member/2]).

:- dynamic(isetlog/2).
:- dynamic(ctx/1).

:- dynamic(filter_on/0).      %filtering rules file: loaded
:- dynamic(size_solver_on/0). %advanced size solver file: loaded
:- dynamic(type_checker/0).   %type-checker file: loaded
:- dynamic(vcg/0).            %verification condition generator (vcg) file: loaded

:- dynamic(final/0).          %default: no final
:- dynamic(nowarning/0).      %default: warning
:- dynamic(nolabel/0).        %default: label
:- dynamic(noneq_elim/0).     %default: neq_elim
:- dynamic(noran_elim/0).     %default: ran_elim
:- dynamic(nocomp_elim/0).    %default: comp_elim
:- dynamic(noirules/0).       %default: irules
:- dynamic(trace/1).          %default: no trace

:- dynamic(strategy/1).       %modifiable configuration params
:- dynamic(path/1).
:- dynamic(rw_rules/1).
:- dynamic(fd_labeling_strategy/1).

:- multifile(replace_rule/6).             %in files 'setlog_rules.pl' and 'TTF_rules.pl'    
:- multifile(inference_rule/7).           %in files 'setlog_rules.pl' and 'TTF_rules.pl'
:- multifile(fail_rule/6).                %in files 'setlog_rules.pl' and 'TTF_rules.pl'
:- multifile(equiv_rule/3).               %in files 'setlog_rules.pl' and 'TTF_rules.pl'
:- multifile(setlog_command/1).           %in this file and in file 'setlog_tc.pl'     
:- multifile(ssolve_command/1).           %in this file and in file 'setlog_tc.pl'     


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%                                    %%%%%%%%%%%%%%
%%%%%%%%%%%   {log} interactive environment    %%%%%%%%%%%%%%
%%%%%%%%%%%                                    %%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
% The following predicates implement the {log}
% interactive programming environment. This environment
% offers a Prolog-like user interface, enriched with facilities
% for manipulating sets and multi-sets. The most notable         %DA AGGORNARE
% syntactic differences w.r.t. std Prolog are: the use of '&' in
% place of ',' to represent goal conjunction; the  use of 'or'
% in place of ';' to represent goal disjunction; the use of
% 'neg' or 'naf' in place of '\+' to represent negation (resp.,
% simplified Constructive Negation and Negation as Failure).    %DA AGGORNARE
% To enter the {log} interactive environment call the goal
% 'setlog.'. To exit, call the goal 'halt.'.
% N.B. {log}, in the current version, provides only a small
% subset of Prolog built-ins and no support for program
% debugging at {log} program level.
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

setlog :-
    set_default,
    top_level.
 
set_default :-
    set_default_control,
    cond_retract(nolabel),           %set default value: label
    retract_trace,                   %set default value: no trace
    default_int_solver(IS),          
    nb_setval(int_solver,IS).        %set default value for int_solver (clpfd/clpq)
set_default_control :-
    cond_retract(noirules),          %set default value: irules
    cond_retract(noneq_elim),        %set default value: neq_elim
    cond_retract(noran_elim),        %set default value: ran_elim
    cond_retract(nocomp_elim),       %set default value: comp_elim
    default_mode(M), 
    b_setval(smode,M),               %set default value for mode (prover/solver) 
    nb_setval(fix_size,off),         %set default value: nofix_size
    nb_setval(groundsol,off),        %set default value: nogroundsol
    nb_setval(show_min,off),         %set default value: noshow_min
    nb_setval(type_check,off).       %set default value: notype_check

top_level :-
    prompt,
    catch(setlog_read_term(Goal,[variable_names(VarNames)]),  %e.g. input goal:  {X/R}={Y/S} & X neq Y
              setlog_excpt(Msg),excpt_action(Msg)),           % --> Goal: {_16/_18}={_26/_28} & _16 neq _26
                                                              % --> VarNames: [X=_16,R=_18,Y=_26,S=_28]
    (b_getval(type_check,on) ->            
       catch(typecheck(Goal,VarNames),setlog_excpt(Msg),excpt_action(Msg))
    ;
       true        
    ),
    remove_dec(Goal,Goal1),

    extract_vars(Goal1,NonLocalVars),
    remove_local(VarNames,NonLocalVars,VarNamesNL),
    b_setval(varnames,VarNamesNL),     % varnames is used by sat_groundsol

    catch(solve(Goal1,Constr),                         %Goal1: {_16/_18}={_26/_28} & _16 neq _26                         
              setlog_excpt(Msg),excpt_action(Msg)),    % --> Constr: [set(_708),_16 neq _26]
                                                       % --> VarNames: [X=_16,R=_708 with _26,Y=_26,S=_708 with _16]
    skip_return,    
    prepare_answer(Constr,VarNames,VarNames_ext1,Constr1Ext,Vars),
    nl, write_subs_constr(VarNames_ext1,Constr1Ext,Vars), 
    top_level.                                                
top_level :-
    nl, write_no, nl,
    skip_return,
    top_level.

prompt :-
    (  current_prolog_flag(unix, true),!,
       nl, prompt(_,'{log}=> ')
     ;
       current_prolog_flag(windows, true),!,
       nl, write('{log}=> ')
    ).

excpt_action('$aborted') :- !,  
     nl,write('Interrupting goal'),nl,
     abort.
excpt_action('time_out') :- !,  
     nl,write('time_out'),nl,
     abort.
excpt_action(Msg) :-
    nl,write_error(Msg),nl,
    skip_return,
    %top_level.
    fail.   

% remove_local(+VarNames,+NonLocalVars,-NonLocalVarNames)
remove_local([],_,[]).
remove_local([VName=VNo|VarNames],NonLocalVars,[VName=VNo|NonLocalVarNames]) :-
    member_strong(VNo,NonLocalVars),!, 
    remove_local(VarNames,NonLocalVars,NonLocalVarNames).
remove_local([_|VarNames],NonLocalVars,NonLocalVarNames) :-
    remove_local(VarNames,NonLocalVars,NonLocalVarNames).

skip_return :-
    read_pending_codes(user_input,_C,[]).

cond_retract(C) :-
    retract(C),
    !.
cond_retract(_).

retract_trace :-
    retractall(trace(_)).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% read goals %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

setlog_read_term(Goal,Vars) :-
    catch(read_term(Goal,Vars),Msg,syntax_error_msg(Msg)).

syntax_error_msg(_Text) :-
    throw(setlog_excpt('syntax error')).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% prepare answer %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%%% prepare_answer(+Constr,+VarNames,-VarNames_ext1,-Constr1Ext,-Vars) 
%e.g. Constr: [set(_708),_16 neq _26]
%     VarNames: [X=_16,R=_708 with _26,Y=_26,S=_708 with _16]
% --> VarNames_ext1: [R={Y/_N1},S={X/_N1},true,true] 
% --> Constr1Ext: [set(_N1),_30 neq _86]
% --> Vars: [_N1]
prepare_answer(Constr,VarNames,VarNames_ext1,Constr1Ext,Vars) :-  
    add_intv(Constr,ConstrAll,_),
    filter_and_check_w(ConstrAll,RConstrAll,_),                 
    chvar([],_,v(VarNames,RConstrAll),_,_,v(VarNames1,Constr1)),
    postproc(Constr1,Constr1Ext),                                 
    mk_subs_ext(VarNames1,VarNames_ext1),                         
    extract_vars(VarNames_ext1,Vars),                   
    extract_vars(Constr1,ConstrVars),
    rename_fresh_vars(Vars,1,N),
    rename_fresh_vars(ConstrVars,N,_).

add_intv(Constr,ConstrAll,Warning) :-     % same as add_intv_w but without printing
    int_solver(clpfd),!,
    add_FDc(Constr,ConstrAll,Warning).
add_intv(Constr,Constr,_).

filter_and_check_w(Constr,ConstrAll,Warning) :-
    filter_and_check(Constr,ConstrAll,Warning),
    mk_warning(Warning).

filter_and_check(C,NewC,W) :-
    split_cs(C,RedCS),                                    %split the CS into <neq-constraints,other-constraints>
    filter_and_check1(C,RedCS,NewC,W).

filter_and_check1([],_GC,[],_) :- !.
filter_and_check1([C|R],GC,ReducedC,Warning) :-           %remove sort constraints not to be shown
    type_constr(C),
    type_constraints_to_be_shown(LConstr), \+member(C,LConstr),!,
    filter_and_check1(R,GC,ReducedC,Warning).
filter_and_check1([dec(_,_)|R],GC,ReducedC,Warning) :- !, %remove dec/2 constraints   
    filter_and_check1(R,GC,ReducedC,Warning).

filter_and_check1([comp(X,Y,Z)|R],GC,[comp(X,Y,Z)|ReducedC],Warning) :-
    nocomp_elim,                                          %if comp_elim is off, make a warning for goals such as 
    var(Warning),                                         %comp({X/A},{Y/A},{Z/A}) ('possible unreliable answer')
    tail(X,TX),tail(Y,TY),tail(Z,TZ),
    samevar3(TX,TY,TZ),!,
    Warning = unsafe,
    filter_and_check1(R,GC,ReducedC,Warning).
filter_and_check1([C|R],GC,[C|ReducedC],Warning) :-       %if ran_elim is off, make a warning for goals such as 
    noran_elim,                                           %ran(A,{X/A}) ('possible unreliable answer')
    var(Warning),
    is_ran_l(C,_,X,Y),var(X),nonvar(Y),!,
    Warning = unsafe,
    filter_and_check1(R,GC,ReducedC,Warning).
filter_and_check1([C|R],GC,[C|ReducedC],Warning) :-       %if neq_elim is off, make a warning for goals such as  
    noneq_elim,                                           %un(A,B,C) & A neq C ('possible unreliable answer')
    var(Warning),
    is_neq(C,1,W,T),var(W),var(T),
    find_setconstraint(W,T,GC,_X,_Y),!,
    Warning = unsafe,
    filter_and_check1(R,GC,ReducedC,Warning).
filter_and_check1([C|R],GC,[C|ReducedC],Warning) :-       %if neq_elim is off, make a warning for goals such as 
    noneq_elim,                                           %un(A,B,C) & A neq {} ('possible unreliable answer')
    var(Warning),
    is_neq(C,1,W,T), var(W), aggr_term(T),
    find_setconstraint(W,GC),!,
    Warning = unsafe,
    filter_and_check1(R,GC,ReducedC,Warning).

filter_and_check1([X in int(inf,B)|R],GC,[X =< B|ReducedC],Warning) :- !,   %replace open domain declarations
    filter_and_check1(R,GC,ReducedC,Warning).                               %e.g., X in int(inf,10) ---> X =< 10
filter_and_check1([X in int(A,sup)|R],GC,[X >= A|ReducedC],Warning) :- !,   %replace open domain declarations
    filter_and_check1(R,GC,ReducedC,Warning).                               %e.g., X in int(1,sup) ---> X >= 1

% if int_solver(clpq), check that all integer constraints
% contain only linear expressions; otherwise raise a warning
filter_and_check1([glb_state(Rel)|R],GC,[Rel|ReducedC],Warning) :-
    var(Warning),
    int_solver(clpq),!,
    Rel =.. [_OP,E1,E2],                                      
    (is_linear(E1),is_linear(E2) ->
       true
    ;
       Warning = nonlinear
    ),
    filter_and_check1(R,GC,ReducedC,Warning).

filter_and_check1([glb_state(Rel)|R],GC,ReducedC,Warning) :-   %if int_solver is clpfd, remove constraints glb_state(E1 op E2)
    Rel =.. [_OP,E1,E2],                                       %where either E1 or E2 are ground and the other expr. has a 
    int_solver(clpfd),                                         %domain associated with it; e.g., glb_state(X>3) & X in int(10,sup)
    (   ground(E2), get_domain(E1,(E1 in _)) ->
        true
    ;
        ground(E1), get_domain(E2,(E2 in _))
    ),
    !,
    filter_and_check1(R,GC,ReducedC,Warning).
filter_and_check1([glb_state(Rel)|R],GC,[Rel|ReducedC],Warning) :- !, %replace each glb_state(C) with C;
    (   var(Warning),                                                 %if int_solver is clpfd, and C is E1 op E2 generate 
        int_solver(clpfd),                                            %warning if E1 and E2 are not sufficiently instantiated
        Rel =.. [_OP,E1,E2],                                          %e.g  X>Y, X>X-1, X+Y>2 
        (   \+ ground(E1), \+ ground(E2) ->
            true
        ;
            term_variables(Rel,VarsList), VarsList=[_,_|_]
        ) ->
        Warning = 'not_finite_domain'
    ;
        true
    ),
    !,
    filter_and_check1(R,GC,ReducedC,Warning).

filter_and_check1([C|R],GC,[C|ReducedC],Warning) :-
    (   var(Warning), int_solver(clpfd), contains_open_int(C) ->
        Warning = 'not_finite_domain'
    ;
        true
    ),
    !,
    filter_and_check1(R,GC,ReducedC,Warning).

filter_and_check1([C|R],GC,[C|ReducedC],Warning) :-
    filter_and_check1(R,GC,ReducedC,Warning).

contains_open_int(C) :-
    C=..[OP,X,Y],!,
    (OP == subset,! ; OP == dom),     % NOT-SOLVED irreducible constraints which may
    (open_intv(X),! ; open_intv(Y)).  % contain open intervals
%contains_open_int(C) :-
%   C=..[_,X,Y,Z],
%   (open_intv(X),! ; open_intv(Y),! ; open_intv(Z)).

% is_linear(E): true when E is a linear (integer) expression
% E is assumed to be returned by CLP(Q)
% so its form is not as general as it could be
is_linear(E) :- 
    ground(E),!.    % takes care of rational numbers, eg. 1r2
is_linear(E) :- 
    var(E),!.
is_linear(E) :-
    E =.. [O,E1,E2], member(O,[+,-]),!,
    is_linear(E1),
    is_linear(E2).
is_linear(E) :-
    E =.. [-,E1],!,
    is_linear(E1).
is_linear(E) :-         % CLP(Q) returns products with constants at the lhs
    E =.. [*,E1,E2],!,
    ground(E1),
    var(E2).

mk_warning(R) :-
    var(R),
    !.
mk_warning('not_finite_domain') :- !,
    write('\n***WARNING***: non-finite domain'),nl.
mk_warning(unsafe) :- !,
    write('\n***WARNING***: possible unreliable answer'),nl.
mk_warning(nonlinear) :-
    write('\n***WARNING***: non-linear expressions over CLP(Q); possible unreliable answer'),nl.

%mk_subs_ext(+VarSubs,-VarSubsMin)
%e.g. VarSubs: [X=_30,R=_64 with _86,Y=_86,S=_64 with _30] 
% --> VarSubsMin: [R={Y/_64},S={X/_64},true,true]
mk_subs_ext(VarSubs,VarSubsMin) :-
    postproc(VarSubs,VarSubsExt),
    mk_subs_vv(VarSubsExt,VarSubsMin).

mk_subs_vv([],[]).
mk_subs_vv([N1=V1|Subs],R) :-
    var(V1),
    !,
    V1 = N1,
    mk_subs_vv(Subs,SubsMin),
    append(SubsMin,[true],R).
mk_subs_vv([N1=V1|Subs],[N1=V1|R]) :-
    mk_subs_vv(Subs,R).

rename_fresh_vars([],Num,Num).
rename_fresh_vars([X|R],Num,NumF) :-
    var(X),!,
    name(Num,NumCodeList),
    %CodeList = [95,78|NumCodeList],   %_N
    fresh_variable_prefix(Prf),
    append(Prf,NumCodeList,CodeList),
    name(XNew,CodeList),
    X=XNew,
    Num1 is Num + 1,
    rename_fresh_vars(R,Num1,NumF).
rename_fresh_vars([_X|R],Num,NumF) :-
    rename_fresh_vars(R,Num,NumF).

%%%%%%%%%%% write subs and constraints - ask for other solutions %%%%%%%%%%%%

%%% write_subs_constr(+Subs,+Constr,+Vars) 
%e.g. Subs: [R={Y/_N1},S={X/_N1},true,true] 
%     Constr: [set(_N1),_30 neq _86]
%     Vars: [_N1]
%output: R = {Y/_N1},S = {X/_N1}
%        Constraint: set(_N1), X neq Y   
write_subs_constr([],[],_) :-
    !,
    write_yes, nl.
write_subs_constr(Subs,Constr,Vars) :-
    (   Subs = [] ->
        true
    ;
        Subs = [true|_] ->
        write_true, Prn = y
    ;
        write_subs_all(Subs,Prn)
    ),
    write_constr(Constr,Vars,Prn),
    ask_the_user(Prn).

%ask_the_user(+Prn): if Prn is unbound do nothing; otherwise, 
%ask the user for another solution
ask_the_user(Prn) :-
    var(Prn),
    !.
ask_the_user(_) :-
    nl,
    nl, write('Another solution?  (y/n)'),
    get_single_char(C),
    (   C \== 121,!    % 'y'
    ;
        fail
    ).

%write_subs_all(+Subs,-Prn): print all equalities Var=Term in Subs  
%and bind Prn to 'y' if Subs is not empty 
write_subs_all([], _).
write_subs_all([N1=V1|R], Prn) :-
    write(N1), write(' = '), write(V1), Prn = y,
    (   R = [] ->
        true
    ;
        R = [true|_] ->
        true
    ;
        write(',  '), nl, write_subs_all(R,Prn)
    ).

%write_constr(+Constr_ext,+Vars,-Prn): print all constraints in Constr_ext 
%and bind Prn to 'y' if Constr_ext is not empty (Vars is unused)
write_constr(Constr_ext,Vars,Prn) :-
    write_eqconstr_first(Constr_ext,Constr_ext_noeq),
    write_constr_first(Constr_ext_noeq,Vars,Prn).

%TODO - write_eqconstr_first/2: ricerca e stampa le eventuali uguaglianze
%presenti nel constraint calcolato. Sembra inutile:
%non dovrebbero essere presenti uguaglianze nel constraint calcolato e
%anche nel caso ce ne fossero potrebbero essere comunque stampate dalla
%successiva chiamata alla write_constr_first/3.
%Per ora la lascio perchè è necessario controllare meglio.
%Ma nella definizione di str_constr/3 analoga alla write_constr/3, ma
%operante su stringhe, l'analoga della write_eqconstr_first/2 è
%già stata omessa

write_eqconstr_first([], []).               
write_eqconstr_first([T1 = T2|R],NewR) :-   
    var(T1),
    !,
    write(',  '), nl,
    write(T1), write(' = '), write(T2),
    write_eqconstr_first(R,NewR).
write_eqconstr_first([T1 = T2|R],NewR) :-
    var(T2),
    !,
    write(',  '), nl,
    write(T2), write(' = '), write(T1),
    write_eqconstr_first(R,NewR).
write_eqconstr_first([C|R],[C|NewR]) :-
    write_eqconstr_first(R,NewR).

write_constr_first([], _, _).
write_constr_first([C|Constr], Vars, Prn) :-
    nl, write_constraint,
    write_atomic_constr(C), Prn = y,
    write_constr_all(Constr,Vars).

write_constr_all([], _).
write_constr_all([C|Constr], Vars) :-
    write(', '), write_atomic_constr(C),
    write_constr_all(Constr,Vars).

write_atomic_constr(Constr) :-
    simplify_atomic_constr(Constr,SConstr),
    write(SConstr).

simplify_atomic_constr(solved(C,_,_),C) :- !.
simplify_atomic_constr(subset(A,ris(X in B,R,F,P,FP)),SC) :- 
    A == B, X == P, R == [], FP == true,!,
    no_name(X), SC = foreach(X in A,F).
simplify_atomic_constr(subset(A,ris(X in B,R,F,P,FP)),SC) :-
    A == B, X == P, FP == true,!,
    no_name(X), SC = foreach(X in A,R,F,true).
simplify_atomic_constr(subset(A,ris(X in B,R,F,P,FP)),SC) :-
    A == B, X == P, FP = (FP1 & true),!,
    no_name(X), SC = foreach(X in A,R,F,FP1). 
simplify_atomic_constr(C,C).

no_name(X) :-
    var(X),!,
    X='_X'.    
no_name(_).

%%%%%%%%%%% write labels (error, yes, no, constraint, true) %%%%%%%%%%%%

write_error(Msg) :-
    (  current_prolog_flag(unix, true),!,
       ansi_format([bold,bg(white),fg(red)],'***ERROR***: ~w',[Msg])
     ;
       current_prolog_flag(windows, true),!,
       %write('***ERROR***: '), write(Msg)
       ansi_format([bold,fg(red)],'***ERROR***: ~w',[Msg])
    ).

write_no :-
    (  current_prolog_flag(unix, true),!,
       ansi_format([bold,fg(red)],'no',[])
     ;
       current_prolog_flag(windows, true),!,
       %write(no)
       ansi_format([bold,fg(red)],'no',[])
    ).

write_yes :-
    (  current_prolog_flag(unix, true),!,
       ansi_format([bold,fg(green)],'yes',[])
     ;
       current_prolog_flag(windows, true),!,
       %write(yes)
       ansi_format([bold,fg(green)],'yes',[])
    ).

write_constraint :-
    (  current_prolog_flag(unix, true),!,
       ansi_format([bold],'Constraint: ',[])
     ;
       current_prolog_flag(windows, true),!,
       %write('Constraint: ')
       ansi_format([bold],'Constraint: ',[])
    ).

write_true :-
    (  current_prolog_flag(unix, true),!,
       ansi_format([bold,fg(green)],'true',[])
     ;
       current_prolog_flag(windows, true),!,
       %write('true')
       ansi_format([bold,fg(green)],'true',[])
    ).


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%                              %%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%   Using {log} from Prolog    %%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%                              %%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
% The following predicates allow a Prolog program to use the
% {log} facilities for set/bag definition and manipulation,
% without leaving the Prolog execution environment.
% In particular, they provide a (Prolog) predicate for calling
% any {log} goal G, possibly involving {log} set constraints.
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%%%% setlog(+Goal)
%
setlog(Goal) :-
    setlog(Goal,_,_).

%%%% setlog(+Goal,-OutConstrLst)
%
setlog(Goal,OutConstrLst) :-
    setlog(Goal,OutConstrLst,_).

%%%% setlog(+Goal,-OutConstrLst,-Res) 
%%%% Res = success | maybe
%
setlog(Goal,OutConstrLst,Res) :-
    set_default,
    setlog1(Goal,OutConstrLst,Res).

setlog1(Goal,OutConstrLst,Res) :-
    nonvar(Goal),   
    term_variables(Goal,LVars),
    copy_term(Goal,NewGoal),
    term_variables(NewGoal,LVarsNew),
    setlog2(NewGoal,Constr,Res),
    postproc(Constr,OutConstrLst),           %from 'with' to {...} notation
    postproc(LVarsNew,LVarsNew_ext),
    mk_subs(LVars,LVarsNew_ext).           %apply sustitutions to the original variables

setlog2(Goal,Constr,Res) :-
    remove_dec(Goal,Goal1),          
    solve(Goal1,C),                                   
    remove_solved(C,C1),                   %remove info about "solved" constraints
    add_intv(C1,Constr1,Warning),          %add the possibly remaining interval constr's
    filter_and_check(Constr1,Constr,Warning),
    map_warning(Warning,Res).

mk_subs([],[]).                            %mk_subs(L1,L2) unifies each variable in list L1
mk_subs([V|Vars],[T|Terms]) :-             %with the corresponding term in list L2
    V=T,
    mk_subs(Vars,Terms).

map_warning(Warning,maybe) :-
    nonvar(Warning),Warning == 'not_finite_domain',!.
map_warning(Warning,maybe) :-
    nonvar(Warning),Warning == 'unsafe',!.
map_warning(Warning,maybe) :-
    nonvar(Warning),Warning == 'maybe',!.
map_warning(_Warning,success).

%%%% setlog(+Goal,+TimeOut,-OutConstrLst,-Res,+OptList): 
%%%% setlog(+Goal,+TimeOut,-OutConstrLst,-Res,+try([OptList_1,...,OptList_n])): 
%%%% Res = success | time_out | maybe
%%%% setlog with timeout and other optional strategies
%
setlog(Goal,TimeOut,OutConstrLst,Res,Options) :-
    set_default,
    setlog1(Goal,TimeOut,OutConstrLst,Res,Options).
setlog1(Goal,TimeOut,OutConstrLst,Res,[]) :- !,        % no options
    set_default_control,
    setlog_time_out(setlog1(Goal,OutConstrLst,Res1),TimeOut,Res2),
    check_timeout_res(Res2,Res1,Res).

% to allow special option all_prover
% setlog(...,try(prover_all)) = setlog(...,try([subset])), for all subset of
% all_prover_mode_strategies
setlog1(Goal,TimeOut,OutConstrLst,Res,try(prover_all)) :- !,
    all_prover_mode_strategies(All),
    findall(S,setlog:powerset(All,S),PS),
    setlog1(Goal,TimeOut,OutConstrLst,Res,try(PS)).

setlog1(Goal,TimeOut,OutConstrLst,Res,try([OptsLst1|ROpts])) :- !, 
    set_default_control,                               % with the 'try' clause
    setlogTimeOut_opt(OptsLst1,Goal,TimeOut,Constr,Res1),
    setlogTimeOut_cont(ROpts,Goal,TimeOut,Constr,OutConstrLst,Res1,Res).
setlog1(Goal,TimeOut,OutConstrLst,Res,OptsLst) :- !,   % with not empty list of options       
    set_default_control,
    setlogTimeOut_opt(OptsLst,Goal,TimeOut,OutConstrLst,Res).

setlogTimeOut_opt(OptsLst,Goal,TimeOut,Constr,Res) :- 
    activate_opt(OptsLst,[trace,groundsol,type_check]),
    setlog_time_out(setlog1(Goal,Constr,Res1),TimeOut,Res2),
    check_timeout_res(Res2,Res1,Res).

% to allow prover_mode_strategies as options
activate_opt(OptsList,NoOptions) :-
     activate_opt1(OptsList,NoOptions,ProverOptions),
     (ProverOptions \== [] -> 
         b_setval(smode,prover(ProverOptions)) 
     ;
         true
     ).
       
% third argument is ProverOptions (i.e. prover_mode_strategies)
% added third clause; all the rest is equal to old activate_opt/2
activate_opt1([],_,[]):- !.
activate_opt1([Opt|OptsList],NoOptions,ProverOptions) :- 
    setlog_command(Opt),
    \+ member_strong(Opt,NoOptions),!,
    ssolve_command(Opt),
    activate_opt1(OptsList,NoOptions,ProverOptions).
activate_opt1([Opt|OptsList],NoOptions,ProverOptions) :- 
    prover_mode_strategies([Opt]),
    \+ member_strong(Opt,NoOptions),!,
    ProverOptions = [Opt | ProverOptions1],
    activate_opt1(OptsList,NoOptions,ProverOptions1).
activate_opt1(Opt,_,_) :- !,
    throw(setlog_excpt('wrong option'(Opt))).

setlogTimeOut_cont([],_Goal,_TimeOut,Constr,Constr,Return,Return) :- !.
setlogTimeOut_cont(_,_Goal,_TimeOut,Constr,Constr,success,success) :- !.
setlogTimeOut_cont(ROpt,Goal,TimeOut,_,OutConstrLst,_,Res) :-
    setlog1(Goal,TimeOut,OutConstrLst,Res,try(ROpt)).

check_timeout_res(success,Solve_res,Res) :- !,
    map_warning(Solve_res,Res).
check_timeout_res(time_out,_,timeout) :- !. 
check_timeout_res(Timeout_Res,_,Timeout_Res).

setlog_time_out(G,T,R) :-
   (T > 0 -> 
      time_out(G,T,R) 
   ; 
      throw(setlog_excpt('timeout must be a positive number')) 
   ).

%%%% setlog with timeout and default strategies (setlog/4)
%%%% setlog(+Goal,+TimeOut,-OutConstrLst,-Res) (Res = success | time_out | maybe)
%
setlog(Goal,TimeOut,OutConstrLst,Res) :-
    setlog5_opts(Opts_list),
    setlog(Goal,TimeOut,OutConstrLst,Res,Opts_list).

%%%%%%%%%%%%%%%%%%%%%

%%%% setlog_str(GoalString,VarNamesList,ConstrList): 
% same as setlog(Goal,...) but GoalString is a string representing a {log} goal
% and VarNamesList is a list of pairs VarNameAtom = InternalVar where 
% VarNameAtom is the (external) name of a variable in GoalString and InternalVar
% is the corresponding Prolog variable 
%e.g. ?- setlog_str("{X/R}={Y/S} & X neq Y",['X'=X,'A'=A,'S'=S,'R'=R],C,Res).
%     S = {X/_A},
%     R = {Y/_A},
%     C = [set(_A), X neq Y].
%%%% setlog_str(GoalString,EqsString,ConstrString): 
% same as setlog(Goal,...) but GoalString is a string representing a {log} goal and
% EqsString is a string representing the equalities computed by solving GoalString
%e.g. ?- setlog_str("{X/R}={Y/S} & X neq Y",Eqs,C).
%     Eqs = "R = {'Y'/'_N1'}, S = {'X'/'_N1'}",, 
%     C = "set('_N1'), 'X'neq'Y'".

%%%% setlog_str(+GoalString,+VarNamesList) 
%%%% setlog_str(+GoalString,-EqsString)
setlog_str(GoalString,VarNames_or_Eqs) :- 
   setlog_str(GoalString,VarNames_or_Eqs,_,_).

%%%% setlog_str(+GoalString,+VarNamesList,-ConstrList) 
%%%% setlog_str(+GoalString,-EqsString,-ConstrString) 
setlog_str(GoalString,VarNames_or_Eqs,OutConstr) :- 
   setlog_str(GoalString,VarNames_or_Eqs,OutConstr,_).

%%%% setlog_str(+GoalString,+VarNamesList,-ConstrList,-Res) 
%%%% setlog_str(+GoalString,-EqsString,-ConstrString,-Res) 
%%%% Res = success | maybe 
setlog_str(GoalString,VarNames_or_Eqs,OutConstr,Res) :- 
  set_default,
  setlog1_str(GoalString,VarNames_or_Eqs,OutConstr,Res).

setlog1_str(GoalString,VarNames_or_Eqs,OutConstr,Res) :- 
  nonvar(GoalString),                                
  term_string(Goal,GoalString,[variable_names(VN)]), 
  term_variables(VN,LVars),                          
  copy_term([Goal,VN],[NewGoal,NewVN]),              
  term_variables(NewVN,LVarsNew),                       
  setlog2_str(NewGoal,NewVN,Constr,Res),            
  postproc(Constr,Constr_ext),      %from 'with' to {...} notation   
  postproc(LVarsNew,LVarsNew_ext),                   
  (is_list(VarNames_or_Eqs) ->
     mk_subs(LVars,LVarsNew_ext),   %apply sustitutions to the original vars
     vars_match(VarNames_or_Eqs,VN),
     OutConstr = Constr_ext   
  ;  
     postproc(NewVN,NewVN_ext),              
     mk_subs_vv(NewVN_ext,VarNames_ext1),    
     extract_vars(VarNames_ext1,Vars),       
     extract_vars(Constr_ext,ConstrVars),  
     rename_fresh_vars(Vars,1,N),   
     rename_fresh_vars(ConstrVars,N,_),     
     str_subs_constr(VarNames_ext1,Constr_ext,EqsStr,ConstrStr),
     VarNames_or_Eqs = EqsStr,
     OutConstr = ConstrStr
  ).

setlog2_str(Goal,VarNames,Constr,Res) :-   
    (b_getval(type_check,on) ->            
       typecheck(Goal,VarNames)
    ;
       true      
    ),
    remove_dec(Goal,Goal1),
    extract_vars(Goal1,NonLocalVars),
    remove_local(VarNames,NonLocalVars,VarNamesNL),
    b_setval(varnames,VarNamesNL),   % varnames is used by sat_groundsol
    solve(Goal1,C),
    remove_solved(C,C1),             %remove info about "solved" constraints    
    add_intv(C1,Constr1,Warning),    %add the possibly remaining interval constr's
    filter_and_check(Constr1,Constr,Warning),
    map_warning(Warning,Res).

%vars_match(+VarNamesList1,+VarNamesList2)
%VarNamesList1 and VarNamesList2 are list of pairs VarName=InternalVar
%for each pair in VarNamesList1 with the same VarName in VarNamesList2
%unifies the corresponding InternalVar's
%e.g. ?- vars_match(['X'=X,'A'=A,'S'=S],['X'=_1,'S'=_2,'A'=_3])
%     X = _1, A = _3, S = _2 
%If some VarName in VarNamesList1 does not occur in VarNamesList2 or
%if some InternalVar in VarNamesList1 is not a variable then an
%exception is raised.
vars_match([],_) :- !.
vars_match([VarName=InternalVar|VarNamePairs],VarNamesList2) :-
   var(InternalVar),    
   member(VarName=InternalVar,VarNamesList2),!, 
   vars_match(VarNamePairs,VarNamesList2).
vars_match(_VarNamePairs,_VarNamesList2) :-
   throw(setlog_excpt('wrong argument in setlog_tc/3 predicate')).

%str_subs_constr(+Subs,+Constr,-EqsStr,-ConsStr)     
%If Subs is a list of equalities and 'true' atoms (e.g., [R={A/_N1},S={X/_N1},true,true])
%and Constr is a list of constraints (e.g., [set(_N1),X neq A]),
%then EqsStr is a list of strings corresponding to the equalities in Subs different from 'true'
%and ConsStr is a list of strings corresponding to the sonstraints in Constr
%e.g., EqsStr = ["R = {'A'/'_N1'}", "S = {'X'/'_N1'}"], ConsStr = ["set('_N1')", "'X'neq'A'"]
%
str_subs_constr([],[],[],[]) :- !.       
str_subs_constr(Subs,Constr,EqStrs,ConsStrs) :-
    ( Subs = [] -> 
      EqStrs = []  
    ;
      Subs = [true|_] -> 
      EqStrs = []
    ;
    str_subs_all(Subs,EqStrs)
    ),
    str_constr_all(Constr,ConsStrs).

str_subs_all([],[]).
str_subs_all([N1=V1|R],[EqStr1|EqStrs]) :-
    term_string(N1=V1,EqStr1),
    ( R = [] -> EqStrs=[]
    ;
      R = [true|_] -> EqStrs=[]
    ;
     str_subs_all(R,EqStrs)
    ).

str_constr_all([],[]).
str_constr_all([C1|R],[CStr1|ConsStrs]) :-
    str_atomic_constr(C1,CStr1),
    str_constr_all(R,ConsStrs).

str_atomic_constr(Cons,StrCons) :-
    simplify_atomic_constr(Cons,SCons),
    term_string(SCons,StrCons). 

%%%% setlog_str(+GoalString,+VarNamesList,+TimeOut,ConstrList,-Res,+OptList)
%%%% setlog_str(+GoalString,-EqsString,+TimeOut,-ConstrString,-Res,+OptList) 
%%%% Res = success | time_out | maybe
setlog_str(GoalString,VarNames_or_Eqs,TimeOut,OutConstr,Res,Options) :-
    set_default,
    setlog1_str(GoalString,VarNames_or_Eqs,TimeOut,OutConstr,Res,Options).

setlog1_str(GoalString,VarNames_or_Eqs,TimeOut,OutConstr,Res,[]) :- !,     % no options
    set_default_control,
    setlog_time_out(setlog1_str(GoalString,VarNames_or_Eqs,OutConstr,Res1),TimeOut,Res2),
    check_timeout_res(Res2,Res1,Res).
setlog1_str(GoalString,VarNames_or_Eqs,TimeOut,OutConstr,Res,OptsLst) :- !,     
    set_default_control,
    setlogTimeOut_opt(OptsLst,GoalString,VarNames_or_Eqs,TimeOut,OutConstr,Res).

setlogTimeOut_opt(OptsLst,GoalString,VarNames_or_Eqs,TimeOut,Constr,Res) :- 
    activate_opt(OptsLst,[trace]),
    (TimeOut == -1 ->
        setlog1_str(GoalString,VarNames_or_Eqs,Constr,Res1)
     ;
        setlog_time_out(setlog1_str(GoalString,VarNames_or_Eqs,Constr,Res1),TimeOut,Res2)
    ),
    check_timeout_res(Res2,Res1,Res).
 
%%%% setlog_tc(+GoalString,+VarNamesList,-ConstrList): 
%%%% setlog_tc(+GoalString,-EqsString,-ConstrString): 
% same as setlog_str(GoalString,VarNamesList,Cons) 
% but type checking is performed on the input goal
%
setlog_tc(GoalString,VarNames_or_Eqs,OutConstr) :- 
    setlog_str(GoalString,VarNames_or_Eqs,-1,OutConstr,_,[type_check]).

%%%%%%%%%%%%%%%%%%%%%

%%%% rsetlog(+Goal,+TimeOut,-OutConstrLst,-Res,+Options):
% same as setlog/5, with reification on Res
% Res = success | time_out | maybe | failure
%
rsetlog(Goal,TimeOut,OutConstrLst,Res,Options) :-
    set_default,
    nb_setval(sol,no),
    setlog1(Goal,TimeOut,OutConstrLst,Res,Options),
    nb_setval(sol,yes).
rsetlog(_Goal,_TimeOut,_OutConstrLst,failure,_Options) :-
    nb_getval(sol,no).

%%%% rsetlog_str(+GoalString,+VarNamesList,+TimeOut,-ConstrList,-Res,+Options)
%%%% rsetlog_str(+GoalString,-EqsString,+TimeOut,-ConstrString,-Res,+Options)
rsetlog_str(GoalString,VarNames_or_Eqs,TimeOut,OutConstr,Res,Options) :-
    set_default,
    nb_setval(sol,no),
    setlog1_str(GoalString,VarNames_or_Eqs,TimeOut,OutConstr,Res,Options),
    nb_setval(sol,yes).
rsetlog_str(_GoalString,_VarNames_or_Eqs,_TimeOut,_OutConstr,failure,_Options) :-
    nb_getval(sol,no).

%%%%%%%%%%%%%%%%%%%%%

%%%% other predicates for Prolog to {log} interface

setlog_consult(File) :-                   %like setlog(consult(File))
    setlog(consult(File,mute),_).         %but no message is sent to the std output

setlog_clause(Clause) :-                  %for compatibility with previous versions
    setlog(assert(Clause),_).

consult_lib :-                            %to consult the {log} library file
    setlog(consult_lib,_).

setlog_config(ConfigParams) :-            %to modify {log}'s configuration parameters
    set_params(ConfigParams).

setlog_rw_rules :-                        %to load the filtering rule library
    rw_rules(Lib),
    mk_file_name(Lib,FullName),
    consult(FullName).

%%%% auxiliary predicates for Prolog to {log} interface

remove_solved([],[]).
remove_solved([solved(C,_,_)|R],[C|RR]) :-
    !,
    remove_solved(R,RR).
remove_solved([C|R],[C|RR]) :-
    remove_solved(R,RR).

set_params([]).
set_params([P1|ParamsList]) :-
    apply_params(P1),
    set_params(ParamsList).

apply_params(strategy(Str)) :-
    replace_unitCl(strategy(_),Str).
apply_params(path(Path)) :-
    replace_unitCl(path(_),Path).
apply_params(rw_rules(FileName)) :-
    replace_unitCl(rw_rules(_),FileName).
apply_params(fd_labeling_strategy(Str)) :-
    replace_unitCl(fd_labeling_strategy(_),Str).

%%% to be continued

replace_unitCl(Cl,NewParm) :-
    retract(Cl), !,
    Cl =.. [F,_X],
    NewCl =.. [F,NewParm],
    assertz(NewCl).


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%                              %%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%        The help sub-system   %%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%                              %%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

setlog_help :-
    h(setlog).

h(setlog) :-
    nl,
    write('   -   h(syntax), h(constraints), h(builtins), h(lib), h(prolog) to get help '), nl,
    write('       information (resp., about: {log} syntactic convenctions, {log} constraints, '), nl,
    write('       {log} built-in predicates, {log} library predicates, Prolog predicates'), nl,
    write('       for accessing {log})'), nl,
    write('   -   h(all) to get all available help information'), nl,
    write('   -   setlog/0: to enter the {log} interactive environment'),nl.

h(all) :-
    h(syntax),
    h(constraints),
    h(builtins),
    h(prolog),
    h(lib).

h(syntax) :-!,
    nl,
    write('%%%%%%%%%   Syntactic differences w.r.t. std Prolog  %%%%%%%%%'),
    nl, nl,
    write('   - ''&'' is used in place of '','' in clause bodies'), nl,
    write('   - ''or'' is used in place of '';'''),
    write('  to represent goal disjunction.'), nl,
    write('   - neg or naf are used in place of  ''\\+'''),
    write('  to represent negation (resp., '), nl,
    write('     simplified Constructive Negation and Negation as Failure)'),nl,
    write('   - p implies q: implemented as neg(p) or q '),nl,
    write('   - p nimplies q: implemented as p & neg(q) '),nl,
    nl,
    write('   - Interpreted terms.'),
    nl,
    write('     1. Extensional sets:'), nl,
    write('        (a, b, c: any term; R: variable, set, interval, IS, RIS, CP)'), nl,
    write('        - {}: the empty set'), nl,
    write('        - {a,b,c}: the set containing three elements, a, b, c'),nl,
    write('        - {a,b/R}: the set {a,b} U R,'), nl,
%    write('     2. Extensional multisets:'), nl,
%    write('        (a, b, c: any term; R: variable, multiset)'), nl,
%    write('        - *({a,b,b}) (or, * {a,b,b}): the multiset containing the elements,'),nl,
%    write('          ''a'' (1 occurrence) and  ''b'' (2 occurrences)'),nl,
%    write('        - *({a,b/R}): the multiset *({a,b}) U R'), nl,
    write('     2. Intervals:'), nl,
    write('        (h, k: variable, integer number)'), nl,
    write('        - int(h,k): the set of'), nl,
    write('          integer numbers ranging from h to k (k>=h) or the empty set (k<h)'), nl,
    write('     3. Cartesian Products (CP):'), nl,
    write('        (A, B: variable, set, IS)'), nl,
    write('        - cp(A,B): the set {[x,y] : x in A & y in B}'), nl,
    write('     4. Intensional Sets (IS):'), nl,
    write('        (X: variable; G: any {log} goal containing X)'), nl,
    write('        - {X : (G)}'), nl,
    write('        - {X : exists(V,G)}, V variable local to G'), nl,
    write('        - {X : exists([V1,...,Vn],G)}, V1,...,Vn variables local to G'), nl,
    write('     6. Restricted Intensional Sets (RIS):'), nl,
    write('        - ris(C in D,[V1,...,Vn],G,t,FP): the set'), nl,
    write('             {Y : exists([C,V1,...,Vn],C in D & G & Y=t & FP)}'), nl,
    write('             ([V1,...,Vn], FP optional)'), nl,
    write('        - ris(C in D,[V1,...,Vn],G): the set'), nl,
    write('             {Y : exists([C,V1,...,Vn],C in D & G & Y=C)}'), nl,
    write('             ([V1,...,Vn] optional)'), nl,
    write('          + C: control term, can be'), nl,
    write('               X, [X,Y], {X/Y},'), nl,
    write('               or any nested list of distinct variables;'), nl,
    write('          + D: domain, can be'), nl,
    write('               variable, set, interval, RIS, CP; '), nl,
    write('          + V1,...,Vn: parameters, variables local to G'), nl,
    write('          + G: filter, any {log} goal'), nl,
    write('          + t: pattern, any term but not a RIS'), nl,
    write('          + FP: functional predicates, any {log} goal'), nl,
    write('   - Restricted Universal Quantifiers (RUQ): '), nl,
    write('       (A: variable, set, multiset, list, interval, IS)'), nl,
    write('        - forall(X in A, G): X variable and G any {log} goal containing X'), nl,
    write('        - forall(X in A, exists(V,G))'),nl,
    write('        - forall(X in A, exists([V1,...,Vn],G)):'), nl,
    write('            V1,...,Vn variables local to G'), nl,
    nl.
h(constraints) :-!,
    nl,
    write('%%%%%%%%%   {log} constraints  %%%%%%%%%'),
    nl, nl,
    write('   1.  General constraints:'), nl,
    write('       (u: any term; t: any term but not a CP nor a RIS; '), nl,
    write('        A: variable, set, multiset, list, interval, CP, IS, RIS)'), nl,
    write('        - u1 = u2: equality'), nl,
    write('        - u1 neq u2: non-equality'), nl,
    write('        - t in A: membership'), nl,
    write('        - t nin A: non-membership'), nl,
    nl,
    write('   2.  Set constraints:'), nl,
    write('       (A, B, C: variable, set, interval, IS, CP) '), nl,
    write('        - un(A,B,C)/nun(A,B,C): union/not-union'), nl,
    write('        - disj(A,B)/ndisj(A,B): disjointness/non-disjointness'), nl,
    write('        - inters(A,B,C)/ninters(A,B,C): intersection/not-intersection'), nl,
    write('        - subset(A,B)/nsubset(A,B): subset/not-subset'), nl,
    write('        - ssubset(A,B): strict subset'), nl,
    write('        - diff(A,B,C)/ndiff(A,B,C): difference/not-difference'), nl,
    write('        - sdiff(A,B,C): symmetric difference'), nl,
    write('        - less(A,t,B): element removal; t any term'), nl,
    write('       (D: variable, set, interval, IS; '), nl,
    write('        Aint: variable, interval, set or IS of non-negative integers; '), nl,
    write('        n: variable, integer constant)'), nl,
    write('        - size(D,n): set cardinality'), nl,
    write('        - sum(Aint,n): sum all elements (non-negative integers only)'), nl,
    write('        - smin(Aint,n): minimum element'), nl,
    write('        - smax(Aint,n): maximum element'), nl,
    write('       (u: any term) '), nl,
    write('        - set(u)/nset(u): u is/is not a set'), nl,
    write('        - pair(u)/npair(u): u is/is not a pair'), nl,
%    write('        - bag(u) (u is a multiset)'), nl,
%    write('        - list(u) (u is a list)'), nl,
    nl,
    write('   3.  Integer constraints:'), nl,
    write('       (e1, e2: integer expressions; n: variable or integer constant)'), nl,
    write('        - n is e1: equality, with evaluation of expression e'), nl,
    write('        - e1 =< e2: less than or equal to'), nl,
    write('        - e1 < e2: less than'), nl,
    write('        - e1 >= e2: greater than or equal to'), nl,
    write('        - e1 > e2: greater than'), nl,
    write('        - e1 =:= e2: equal'), nl,
    write('        - e1 =\\= e2: not equal'), nl,
    write('        - integer(n)/ninteger(n): n is/is not an integer number'), nl,
    nl,
    write('   4.  Binary relation constraints:'), nl,
    write('       (A,B: variable, set, interval, IS, CP;'), nl,
    write('        R,S,T: variable, binary relation, CP; u: any term) '), nl,
    write('        - dom(R,A)/ndom(R,A): domain/not-domain'), nl,
    write('        - inv(R,S)/ninv(R,S): inverse/not-inverse'), nl,
    write('        - ran(R,A)/nran(R,A): range/not-range'), nl,
    write('        - comp(R,S,T)/ncomp(R,S,T): composition/not-composition'), nl,
    write('        - id(A,S)/nid(A,S): identity relation/not-identity relation'), nl,
    write('        - dres(A,R,S)/ndres(A,R,S): domain restriction/not-domain restriction'), nl,
    write('        - rres(R,A,S)/nrres(R,A,S): range restriction/not-range restriction'), nl,
    write('        - dares(A,R,S)/ndares(A,R,S):'), nl,
    write('        -     domain anti-restriction/not-domain anti-restriction'), nl,
    write('        - rares(R,A,S)/nrares(R,A,S):'), nl,
    write('        -     range anti-restriction/not-range anti-restriction'), nl,
    write('        - rimg(R,A,B)/nrimg(R,A,B): relational image/not-relational image'), nl,
    write('        - oplus(R,S,T)/noplus(R,S,T): overriding/not-overriding'), nl,
    write('        - rel(u)/nrel(u): u is/is not a binary relation'), nl,
    nl,
    write('   5.  Partial function constraints:'), nl,
    write('       (F,G: variable, partial function; '), nl,
    write('        H: variable, partial function, RIS;'), nl,
    write('        t1,t2: any term but not a CP nor a RIS; u: any term)'), nl,
    write('        - apply(F,t1,t2)/napply(F,t1,t2):'), nl,
    write('              function application/not-function application'), nl,
    write('        - comppf(F,G,t1): functional composition'), nl,
    write('        - dompf(H,t1)/ndompf(H,t1): domain/not-domain of a function'), nl,
    write('        - pfun(u)/npfun(u): u is/is not a partial function'), nl,
    nl,
    write('   6.  Constraints for restricted quantifiers:'), nl,
    write('        - foreach(C in D,G): forall C(C in D ==> G(C))'), nl,
    write('        - foreach(C in D,[V1,...,Vn],G,FP): '), nl,
    write('            forall C(C in D ==> FP(C,V1,...,Vn) & G(C,V1,...,Vn))'), nl,
    write('        - nforeach(C in D,G): exists C(C in D & neg(G(C)))'), nl,
    write('        - nforeach(C in D,[V1,...,Vn],G,FP): '), nl,
    write('            exists C(C in D & FP(C,V1,...,Vn) & neg(G(C,V1,...,Vn)))'), nl,
    write('        - exists(C in D,G): nforeach(C in D,neg(G))'), nl,
    write('        - exists(C in D,[V1,...,Vn],G,FP):'), nl,
    write('            nforeach(C in D,[V1,...,Vn],neg(G),FP)'), nl,
    write('          + C: control term as in RIS'), nl,
    write('          + D: domain as in RIS'), nl,
    write('          + V1,...,Vn: parameters as in RIS'), nl,
    write('          + G: filter as in RIS'), nl,
    write('          + FP: functional predicates as in RIS'), nl,
    write('          + For help on RIS see h(syntax)'),
    nl.
h(builtins) :-!,
    h(sbuilt),
    h(pbuilt).
h(sbuilt) :-!,
    nl,
    write('%%%%%%%%% {log} specific built-in predicates %%%%%%%%%'),
    nl, nl,
    write('   -   halt/0: to leave the {log} interactive environment'),nl,
    write('               (go back to the host environment) '), nl,
    write('   -   help/0: to get general help information about {log}'), nl,
    write('   -   prolog_call(G): to call any Prolog goal G from {log}'),nl,
    write('   -   call(G), call(G,C): to call a {log} goal G, possibly getting constraint C'),nl,
    write('   -   solve(G): like call(G) but all constraints generated'),nl,
    write('   -     by G are immediately solved'),nl,
    write('   -   consult_lib/0: to consult the {log} library file setloglib.slog'),nl,
    write('   -   add_lib(F): to add any file F to the {log} library '),nl,
    write('   -   G!: to make a {log} goal G deterministic'), nl,
    write('   -   delay(G,C): to delay execution of G until either C holds or '),nl,
    write('         the computation ends (G, C {log} goals)'), nl,
    write('   -   labeling(X): to force labeling for the domain variable X'),nl,
    write('   -   strategy(S): to change goal atom selection strategy to S'),nl,
    write('         S: cfirst, ordered, cfirst(list_of_atoms)'), nl,
    write('   -   noirules/0, irules/0: to deactivate/activate inference rules '),nl,
    write('         default: irules'), nl,
    write('   -   nolabel/0, label/0: to deactivate/activate labeling on integer variables'),nl,
    write('         default: label - possible unreliable solutions when nolabel'), nl,
    write('   -   noneq_elim/0, neq_elim/0: to deactivate/activate elimination of '),nl,
    write('         neq-constraints '), nl,
    write('         default: neq_elim - possible unreliable solutions when noneq_elim'), nl,
    write('   -   noran_elim/0, ran_elim/0: to deactivate/activate elimination of '),nl,
    write('         ran-constraints of the form ran(R,{...})'), nl,
    write('         default: ran_elim - possible unreliable solutions when noran_elim'), nl,
    write('   -   notrace/0, trace(Mode): to deactivate/activate constraint solving tracing'),nl,
    write('         Mode=sat: general - Mode=irules: inference rules only'), nl,
    write('         default: notrace'), nl,
    write('   -   time(G,T): to get CPU time (in milliseconds) for solving goal G'),nl,
    write('   -   int_solver(Solver): to change the integer solver'),nl,
    write('         Solver=clpq: CLP(Q); Solver=clpfd: CLP(FD)'),nl,
    write('         default: clpq'), nl,
    write('   -   mode(Mode): to change the solving strategy'),nl,
    write('         Mode = solver|prover|prover(S), S any list of'),nl,
    write('                subset_unify|comp_fe|un_fe'),nl,
    write('         default: prover([])'), nl,                                       
    nl.
h(pbuilt) :-!,
    nl,
    write('%%%%%%%% Prolog-like built-in predicates (redefined in {log} %%%%%%%%'),
    nl, nl,
    write_built_list,
    write('   -   read/1'),nl,
    write('   -   write/1'),nl,
    write('   -   call/1'),nl,
    write('   -   assert/1'),nl,
    write('   -   consult/1'),nl,
    write('   -   listing/0'),nl,
    write('   -   abolish/0'),nl.
h(lib) :-!,
    nl,
    write('%%%%%%%% {log} library %%%%%%%%'), nl, nl,
    check_lib,
    nl.
h(prolog) :-!,
    nl,
    write('%%%%%%%% Prolog predicates for accessing {log} facilities %%%%%%%%%'),
    nl,nl,
    write('   -   setlog/0: to enter the {log} interactive environment'),nl,
    write('   -   setlog(G), setlog(G,C): to call a {log} goal G, '), nl,
    write('         possibly getting an (output) {log} constraint C'), nl,
    write('   -   setlog_consult(F): to consult a {log} file F '),nl,
    write('   -   consult_lib: to consult the {log} library file '),nl,
    write('   -   setlog_clause(Cl): to add a {log} clause Cl to the current {log} program '),nl,
    write('   -   setlog_config(list_of_params): to modify {log} configuration parameters '),nl,
    write('         parameters: strategy(S), path(Path), rw_rules(File)'), nl,
    write('   -   setlog_rw_rules: to load the filtering rule library'),
    nl.
h(_) :-
    throw(setlog_excpt('invalid argument')).

write_built_list :-
    sys(N,Ar),
    write('   -   '),write(N),write('/'),write(Ar),nl,
    fail.
write_built_list.

check_lib :-
    isetlog((setlog_lib_help :- _),_),!,
    solve(setlog_lib_help,_).
check_lib :-
    write('{log} library predicates not available'),nl,
    write('Type consult_lib to load the {log} library '),nl.


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%                              %%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%     The inference engine     %%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%                              %%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%%%% solve(+Goal,-Constraint)            Goal: {log} goal in external form
%
solve(Goal_int_ruq,Constr) :-
    set_initial_values,
    transform_goal(Goal_int_ruq,GoalNew),
    %DBG nl,write('NEW GOAL: '),write(GoalNew),nl,
    solve_goal_fin(GoalNew,Constr).

set_initial_values :-
    cond_retract(nowarning),         % set initial value: warning (used to avoid duplicate warnings)
    nb_setval(subset_int,false),     % set initial value: no subset(S,int(A,B)) found 
    nb_setval(minsol,[]),            % set initial value: no minimal solution (=empty list)
    nb_setval(rw_int,[]),            % set initial value: no int(A,B) found (=empty list)
    nb_setval(using_size_solver,false),   
    cond_retract(final).             % set initial value: nofinal
/*
rw_int represents a partial function from terms of the form int(A,B),
with A and B variables, onto variables. It will be implemented as a
list of ordered pairs of the form [int(A,B),X].
%
Such an ordered pair is added to rw_int the first time the term 
int(A,B) is substituted, in the formula, by variable X by means of 
the equivalence:
%
A =< B ==>
  X = int(A,B) <==> subset(X,int(A,B)) & size(X,B-A+1)
%
In this way, the next time int(A,B) is found in the formula it is
looked up in rw_int and X is used in place of int(A,B).
*/ 

%%%% solve_goal_fin(+Goal,-Constraint)    % Goal: {log} goal in internal form
%                                         % (used in solve/2, ssolve/3 (time, solve), 
solve_goal_fin(true,[]) :- !.             % naf_negate/2, solve_SF/6)             
solve_goal_fin(false,_) :- !,fail.
solve_goal_fin(G,ClistNew) :-
    constrlist(G,GClist,GAlist),
    solve_goal_constr_nf(GClist,GAlist,Clist),
    %final_solve(Clist,ClistNew).  
    final_solve(Clist,ClistNew1),
    remove_delay(ClistNew1,ClistNew2),
    sat(ClistNew2,ClistNew3,f),     
    (nb_getval(groundsol,on) ->
       sat_groundsol(ClistNew3,ClistNew)
    ;
       ClistNew = ClistNew3
    ).

% sat_groundsol(SFC,SFCFinal)
% - SFC is the current constraint store
% - SFCFinal is the constraint store after grounding all
%   the variables in SFC. it should always be empty.
% grounding is performed in 4 phases:
% (a) all set variables are bound to the empty set
% (b) if there's at least one integer constraint in SFC,
%     all the integer variables in SFC are bound to the
%     vertex returned by bb_inf when solving the clp(q)
%     constraint store assuming all the variables there
%     are integers
% (c) if there's no integer constraint in SFC but there
%     are still integer(_) constraints in SFC, all
%     these integer variables are bound to values
%     starting from 0 but different from all the integer
%     values appearing in the neq constraints in SFC
% (d) at this point all the set and integer variables
%     have been grounded. there remain non-set,
%     non-integer variables. these variables are bound
%     to values of the form n<number>, where <number>
%     starts at 0 and all the n<number> constants are
%     different from the constants appearing in the neq
%     constraints in SFC. note that npair(n<number>) and
%     ninteger(n<number>) are both true.
%
% (the next numbers refer to the code of sat_groundsol/2)
% (1) ground all the set variables and   
%     all the integer variables if there's at least one
%     integer constraint
% (2) at this point there remain variables in neq,
%     npair, ninteger and, possibly, integer constraints
%     plus variables at the r.h.s. of the equalities
%     whose l.h.s. are the input variables. see the
%     get_neq_int documentation for more details
% (3) ground all the integer variables in case there's
%     no integer constraint in SFC
% (4) this predicate is in setlog_tc.pl. in the call
%     we pass NeqConst instead than OtherConst
%     because in typechecker mode NonIntVar may 
%     still contain integer variables because a type
%     declaration is used instead of the integer(_)
%     constraint and so get_neq_int will deem that
%     variable as a non-integer variable.
sat_groundsol(SFC,SFCFinal) :-
  set_to_empty_get_int(SFC,SFCgSet,IntVars),
  (member(glb_state(_),SFC) ->             % if true, then IntVars \== []
     get_groundsol_int(SFCgSet,IntVars,SFCgsi)
  ;
     SFCgsi = SFCgSet
  ),
  sat(SFCgsi,SFCNew,f),   % (1)
  get_neq_int(SFCNew,NeqVar,NeqConst,IntVar1),  % (2)
  include(integer,NeqConst,IntConst),      % all the integer constants
  exclude(integer,NeqConst,OtherConst),    % all the other constants
  (IntVar1 \== [] ->
    term_variables(IntVar1,IntVar),        % avoid repetitions
    gen_int_eq(IntVar,IntConst,0,EqInt),
    append(EqInt,SFCNew,SFCNew2),
    sat(SFCNew2,SFCNew3,f)  % (3)
  ;
    SFCNew3 = SFCNew
  ),
  b_getval(varnames,VN),                   % to get variables at the r.h.s. of equalities
  extract_vars(VN,EqVar),                  % EqVar: only non-local variables
  append(NeqVar,EqVar,NonIntVar1),
  (NonIntVar1 \== [] ->
    term_variables(NonIntVar1,NonIntVar),  % avoid repetitions
    (nb_getval(type_check,off) ->
       gen_other_eq(NonIntVar,OtherConst,n,0,EqOther)
    ;
       gen_typed_eq(NonIntVar,NeqConst,VN,n,0,EqOther)  % (4)
    ),
    append(EqOther,SFCNew3,SFCNew4),
    sat(SFCNew4,SFCFinal,f)                % ground all non-integer variables
  ;
    SFCFinal = SFCNew3
  ).

% set_to_empty_get_int(CS,CSSet,IV)
% - CS is the current constraint store
% - CSSet adds to CS one S={} constraint for each set(S) in CS
% - IV is a list containing the integer variables present in CS
%   collected by looking for integer(_) constraints
%   not using collect_integer/2 to make all in one pass
set_to_empty_get_int([],[],[]).
set_to_empty_get_int([C|SFC],[C,S={}|SFCSet],IntVars) :-
  member(C,[set(S),pfun(S),rel(S)]),!,
  set_to_empty_get_int(SFC,SFCSet,IntVars).
set_to_empty_get_int([C|SFC],[C|SFCSet],[I|IntVars]) :-
  C = integer(I),!,
  set_to_empty_get_int(SFC,SFCSet,IntVars).
set_to_empty_get_int([C|SFC],[C|SFCSet],IntVars) :-
  set_to_empty_get_int(SFC,SFCSet,IntVars).

% get_groundsol_int(SFCgSet,IntVars,SFCgsi)
% - SFCgSet is the constraint store where set variables
%   have been bound (grounded) to the empty set
% - IntVars is a list containing all the integer variables
%   in SFCgSet. this argument is always non empty
% - SFCgsi equals SFCgSet plus a list of equalities
%   grounding all the variables in IntVars
% (1) the call to sat is due to errors in CLP(Q)
%     if those errors are fixed, the call can be
%     removed
% TODO: bb_inf is called many times before get_groundsol_int
% the problem is that in those calls we don't save
% the Vertex. If we do that, we don't need to call bb_inf here
get_groundsol_int(SFCgSet,[X|IntVars],SFCg) :-
  bb_inf_all([X|IntVars],[X|IntVars],_,Vertex),
  get_min_sol([X|IntVars],[X|IntVars],Vertex,MinSol), 
  append(SFCgSet,MinSol,SFCg),
  sat(SFCg,_,f),!.   % (1)
% this next clause is due to errors in CLP(Q)
% it can be deleted when CLP(Q) gests fixed
get_groundsol_int(SFCgSet,[X|IntVars],SFCg) :-
  mk_sum_to_minimize([X|IntVars],Sum),
  bb_inf_all([X|IntVars],[X|IntVars],Sum,Vertex),
  get_min_sol([X|IntVars],[X|IntVars],Vertex,MinSol), 
  append(SFCgSet,MinSol,SFCg),
  sat(SFCg,_,f),!.

% get_neq_int(SFCNew,NeqVar,NeqConst,IntVar)
% - SFCNew is the constraint store
% - NeqVar list of variables appearing in non integer(_) constraints
%   non integer(_) constraints at this point: neq, npair, ninteger
% - NeqConst list of constants appearing in neq constraints
% - IntVar list of variables appearing in integer(_) constraints
get_neq_int([],[],[],[]) :- !.
get_neq_int([X neq Y|SFCNew],[X,Y|NeqVar],NeqConst,IntVar) :-
  var(Y),!,
  get_neq_int(SFCNew,NeqVar,NeqConst,IntVar).
get_neq_int([X neq Y|SFCNew],[X|NeqVar],[Y|NeqConst],IntVar) :- !,
  get_neq_int(SFCNew,NeqVar,NeqConst,IntVar).
get_neq_int([ninteger(X)|SFCNew],[X|NeqVar],NeqConst,IntVar) :- !,
  get_neq_int(SFCNew,NeqVar,NeqConst,IntVar).
get_neq_int([npair(X)|SFCNew],[X|NeqVar],NeqConst,IntVar) :- !, 
  get_neq_int(SFCNew,NeqVar,NeqConst,IntVar).
get_neq_int([integer(X)|SFCNew],NeqVar,NeqConst,[X|IntVar]) :- !,
  get_neq_int(SFCNew,NeqVar,NeqConst,IntVar).
% TODO: dec/2 should'n have been removed at this point?  %TODO
get_neq_int([dec(_,_)|SFCNew],NeqVar,NeqConst,IntVar) :-
  get_neq_int(SFCNew,NeqVar,NeqConst,IntVar).

% gen_int_eq(IntVar,IntConst,0,EqInt)
% - IntVar list of integer variables
% - IntConst list of integer constants
% - EqInt list of X = y where X in IntVar, y nin IntConst
%   y starts in 0 and is increased until all variables
%   in IntVar are bound to a value
% That is this predicate generates integer constants
% that are different from other integer constants appearing
% in the constraint store, and then binds integer variables
% with these constants. in this way if the goal is
% integer(X) & X neq 0 & X neq 1 & X neq 2, X is bound to 3.
% since there's a finite number of neq constraints 
% gen_int_eq will eventually generate a value for all
% the integer variables
gen_int_eq([],_,_,[]) :- !.
gen_int_eq([X|IntVar],IntConst,N,[X=N|EqInt]) :-
  \+member(N,IntConst),!,
  N1 is N + 1,
  gen_int_eq(IntVar,IntConst,N1,EqInt).
gen_int_eq(IntVar,IntConst,N,EqInt) :-
  N1 is N + 1,
  gen_int_eq(IntVar,IntConst,N1,EqInt).

% gen_other_eq(NonIntVar,OtherConst,n,0,EqInt)
% - NonIntVar list of non-integer variables
% - OtherConst list of non-integer constants
% - EqOther list of X = y where X in NonIntVar, y nin OtherConst
%   y starts in n0 and the number (0) is increased 
%   until all variables in NonIntVar are bound to a value
% That is this predicate generates non-integer constants
% that are different from other non-integer constants appearing
% in the constraint store, and then binds non-integer variables
% with these constants
% all the constants generated here are of the form n<number>
% where <number> starts at 0
gen_other_eq([],_,_,_,[]) :- !.
gen_other_eq([X|NonIntVar],OtherConst,L,N,[X=C|EqOther]) :-
  atomic_list_concat([L,N],C),
  \+member(C,OtherConst),!,
  N1 is N + 1,
  gen_other_eq(NonIntVar,OtherConst,L,N1,EqOther).
gen_other_eq(NonIntVar,OtherConst,L,N,EqOther) :-
  N1 is N + 1,
  gen_other_eq(NonIntVar,OtherConst,L,N1,EqOther).

remove_delay([],[]).
remove_delay([delay(C,_)|R],[C|RR]) :-
    !,
    remove_delay(R,RR).
remove_delay([C|R],[C|RR]) :-
    remove_delay(R,RR).   
  
%%%% solve_goal_constr_nf(+Constraint,+Non_Constraint,-Constraint)
%
solve_goal_constr_nf(Clist,[],CListCan) :- !,
    sat(Clist,CListCan,nf).
solve_goal_constr_nf(Clist,[true],CListCan) :- !,
    sat(Clist,CListCan,nf).
solve_goal_constr_nf(Clist,[A|B],CListOut) :-
    sat(Clist,ClistSolved,nf),
    sat_or_solve(A,ClistSolved,ClistNew,AlistCl,nf),
    append(AlistCl,B,AlistNew),
    solve_goal_constr_nf(ClistNew,AlistNew,CListOut).

sat_or_solve(A,Clist_in,Clist_out,[],F) :-
    nonvar(A), atomic_constr(A),!,
    sat([A|Clist_in],Clist_out,F).
sat_or_solve(A,Clist_in,Clist_out,Alist_out,_) :-
    ssolve(A,ClistCl,Alist_out),
    append(Clist_in,ClistCl,Clist_out).

%%%% final_solve(+Constraint,-NewConstraint)       
%
final_solve([],[]) :- !.
final_solve(C,SFC) :-
   final_sat(C,SFC1),
   ( nb_getval(type_check,on) ->
        %DBG write('constraint sent to the type-checker: '),write(SFC1),nl,   
        check_finite_types(SFC1,F),
        sat_check(F)
   ;
        true
   ),
   (size_solver_on ->
    nb_getval(fix_size,Fix),
    nb_getval(show_min,Show),
    nb_getval(subset_int,SI), 
    b_getval(minsol,MinSol0),
    clean_minsol(MinSol0,MinSol),
    %DBG write('final_solve '),write(MinSol),nl, 
    %DBG write('subset_int '),write(SI),nl,
    (SI == true, Fix == on ->   
        append(MinSol,SFC1,SFC2),
        sat(SFC2,SFC,f)
    ;
        (SI == true ->
            append(MinSol,SFC1,CC2),
            sat_check(CC2)
        ;
            true
        ),
        ((Fix == on,! ; Show == on) ->
            append(MinSol,SFC1,SFC2),
            (Fix == on ->
                 sat(SFC2,SFC,f)
            ;
                 SFC=SFC2
            )
         ;
            SFC=SFC1
         )
     )
   ;
    SFC=SFC1
   ),
   nb_setval(subset_int,false).    

%%%% final_sat(+Constraint,-NewConstraint)       
%                                  % used in final_solve/2, sat_riseq/4 (RIS expansion)
final_sat([],[]) :- !.             % stunify_same_var_ris/5, int_unify/3, sat_un/4
final_sat(C,SFC) :-                % post_proc_list/2 (evaluating trivial RIS), first_rest/4
    trace_in(C,3),
    nb_setval(subset_int,false), 
    final_sat2(C,SFC),
    trace_out(SFC,3).

final_sat2([],[]) :-!.
final_sat2(C,SFC) :-
    finalize_int_constr(C,_),       % finalize integer constraint processing
    set_final,
    sat(C,RevC,f),                  % call the constraint solver (in 'final' mode);
    final_sat_cont2(RevC,C,SFC).

final_sat_cont2(RevC,C,RevC) :-
    RevC == C,!,
    cond_retract(final).
final_sat_cont2(RevC,_C,SFC) :-     % RevC is the resulting constraint;
    final_sat2(RevC,SFC).           % otherwise, call 'final_sat' again

set_final :-
    final,
    !.
set_final :-
    assertz(final).

%%%%

sat_check(C) :-                     % check if C is satisfiable (one solution is enough), 
    copy_term(C,CC,AttrGoalList),   % without instantiating variables in C
    maplist(call,AttrGoalList),
    sat(CC,_,f),!.       

%%%%

clean_minsol([],[]) :- !.
clean_minsol([X = C|MinSol],[X = C|MinSol_]) :-
   var(X),!,
   clean_minsol(MinSol,MinSol_).
clean_minsol([_ = _|MinSol],MinSol_) :-
   clean_minsol(MinSol,MinSol_).

%%%% constrlist(+Atom_conj,-Constraint_list,-Constraint/Non_Constraint_list)
%
constrlist(A,CList,C_NCList) :-
    constrlist(A,CList,StdC_NCList,SpecC_NCList),
    append(SpecC_NCList,StdC_NCList,C_NCList).

constrlist(A & B,[A|B1],B2,B3) :-
    selected_atomic_constr(A),!,
    constrlist(B,B1,B2,B3).
constrlist(A & B,B1,B2,[A|B3]) :-
    selected_user_atom(A),!,
    constrlist(B,B1,B2,B3).
constrlist(A & B,CListAB,NCList1AB,NCList2AB) :-
    nonvar(A), A = (_A1 & _ARest),!,
    constrlist(A,CListA,NCList1A,NCList2A),
    constrlist(B,CListB,NCList1B,NCList2B),
    append(CListA,CListB,CListAB),
    append(NCList1A,NCList1B,NCList1AB),
    append(NCList2A,NCList2B,NCList2AB).
constrlist(A & B,B1,[A|B2],B3) :-
    !,constrlist(B,B1,B2,B3).
constrlist(A,[A],[],[]) :-
    selected_atomic_constr(A),!.
constrlist(A,[],[],[A]) :-
    selected_user_atom(A),!.
constrlist(A,[],[A],[]).

selected_atomic_constr(A) :-
    strategy(cfirst),!,        %% cfirst: select primitive constraints first
    nonvar(A),atomic_constr(A).
selected_atomic_constr(A) :-
    strategy(cfirst(_)),!,
    nonvar(A),atomic_constr(A).
selected_atomic_constr(A) :-
    strategy(ordered),!,       %% ordered: select all atoms in the order they occur
    nonvar(A),A = (_ = _).

selected_user_atom(A) :-
    strategy(cfirst(LAtoms)),  %% cfirst(LAtoms): select atoms in LAtoms just after primitive constraints
    nonvar(A),member(A,LAtoms).

%%%% solve_goal_nf(+Goal,-Constraint)       % Goal: {log} goal in internal form
%                                           % Same as solve_goal_fin/2 but without
solve_goal_nf(true,[]) :- !.                % calling final_solve (used in meta-predicates: ssolve/3,
solve_goal_nf(false,_) :- !,fail.           % sat_delay/4)
solve_goal_nf(G,ClistNew) :-
    constrlist(G,GClist,GAlist),
    solve_goal_constr_nf(GClist,GAlist,ClistNew).

%%%% solve_goal_fin_constr(+GConstraintList,+GAtomList,ConstraintListNew)     
%                                                    % Same as solve_goal_fin/2 but taking
solve_goal_fin_constr(GClist,GAlist,ClistNew) :-     % a list of atoms and a list of constraints 
    solve_goal_constr_nf(GClist,GAlist,Clist),          % instead of a conj. of atoms and constr's (i.e. a goal)     
    final_solve(Clist,ClistNew).                     % (used in c_negate/2, solve_SF/6, solve_RUQ/5)                    


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%% Solving (single) predefined predicates %%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%%%% ssolve(+Atom,-Constraint,-Non_Constraint)
%
ssolve(true,[],[]) :- !.                       
ssolve(false,[],[]):- !, fail.
ssolve(A,C,[]) :-                  %% {log} meta-predicates
    meta_pred(A),!,
    ssolve_meta(A,C).
ssolve(A,C,[]) :-                  %% {log} specific built-in predicates
    sys_special(A),!,
    ssolve_special(A,C).
ssolve(A,[],[]) :-                 %% Prolog built-in predicates
    functor(A,F,N),
    sys(F,N),!,
    call(A).
ssolve(A,[],[]) :-                 %% {log} commands
    setlog_command(A),!,
    ssolve_command(A).
ssolve(A,C,D) :-                   %% program defined predicates
    our_clause(A,B,C1),
    constrlist(B,C2,D),
    append(C1,C2,C).
ssolve(A,_C,_D):-
    functor(A,Pname,N),
    functor(P,Pname,N),
    \+isetlog((P :- _B),_),
    throw(setlog_excpt('undefined procedure'(Pname/N))).

our_clause(A,B,C) :-
    functor(A,Pname,N),
    functor(P,Pname,N),
    isetlog((P :- B),_),
    sunify(P,A,C).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% {log} meta-predicates

meta_pred(naf _) :- !.
meta_pred((_ or _)) :- !.
meta_pred(call(_)) :- !.
meta_pred(call(_,_)) :- !.
meta_pred(solve(_)) :- !.
meta_pred((_)!) :- !.
meta_pred(prolog_call(_)) :- !.
meta_pred(ruq_call(_,_,_)) :- !.            %% for internal use only
meta_pred(sf_call(_,_,_,_)) :- !.           %% for internal use only
meta_pred(cneg _) :- !.                     %% simplified constructive negation - for internal use only

ssolve_meta(naf A,ClistNew) :-              %% negation as failure
    !,naf_negate(A,ClistNew).
ssolve_meta(cneg A,ClistNew) :-             
    !,c_negate(A,ClistNew).

ssolve_meta((G1 or G2),ClistNew) :- !,      %% goal disjunction
    (   solve_goal_nf(G1,ClistNew)
    ;   solve_goal_nf(G2,ClistNew)
    ).

ssolve_meta(call(A),C) :-                   %% meta call
     !,solve_goal_nf(A,C).
ssolve_meta(call(A,C),C) :-                 %% meta call
     !,solve_goal_nf(A,C).

ssolve_meta(solve(A),C) :- !,               %% forces goal A to be completely solved
    b_getval(smode,Current),
    b_setval(smode,solver),
    solve_goal_fin(A,C),
    b_setval(smode,Current).

ssolve_meta((A)!,C) :-                      %% deterministic call
    !,solve_goal_nf(A,C),!.

ssolve_meta(ruq_call(S,InName,VarList),Cout) :- !,      %% RUQs
    solve_RUQ(S,InName,VarList,[],Cout).

ssolve_meta(sf_call(S,GName,PName,VarList),Cout) :- !,  %% SF
    solve_SF(S,GName,PName,VarList,[],Cout).

ssolve_meta(prolog_call(A),[]) :-           %% Prolog call (any predicate)
    nonvar(A),!,
    call(A).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% {log} commands

setlog_command(label) :- !.
setlog_command(nolabel) :- !.
setlog_command(trace(_)) :- !.
setlog_command(notrace) :- !.
setlog_command(neq_elim) :- !.
setlog_command(noneq_elim) :- !.
setlog_command(ran_elim) :- !.
setlog_command(noran_elim) :- !.
setlog_command(comp_elim) :- !.
setlog_command(nocomp_elim) :- !.
setlog_command(irules) :- !.
setlog_command(noirules) :- !.
setlog_command(strategy(_)) :- !.
setlog_command(int_solver(_)) :- !.
setlog_command(final) :- !.
setlog_command(nofinal) :- !.
setlog_command(mode(_)) :- !.
setlog_command(fix_size) :- !.
setlog_command(nofix_size) :- !.
setlog_command(groundsol) :- !.
setlog_command(nogroundsol) :- !.
setlog_command(show_min) :- !.
setlog_command(noshow_min) :- !.
setlog_command(type_check) :- !.
setlog_command(notype_check) :- !.
setlog_command(vcg(_)) :- !.

ssolve_command(label) :- !,          %% (re-)activate automatic labeling
    cond_retract(nolabel).
ssolve_command(nolabel) :-           %% deactivate automatic labeling
    nolabel,!.
ssolve_command(nolabel) :- !,
    assertz(nolabel).

ssolve_command(notrace) :- !,        %% deactivate constraint solving tracing
    retract_trace.
ssolve_command(trace(sat)) :-        %% activate constraint solving tracing
    trace(sat),!.
ssolve_command(trace(irules)) :-
    trace(irules),!.
ssolve_command(trace(Mode)) :- !,
    (Mode == sat -> true ; Mode == irules),
    assertz(trace(Mode)).

ssolve_command(neq_elim) :- !,       %% (re-)activate automatic neq elimination
    cond_retract(noneq_elim).
ssolve_command(noneq_elim) :-        %% deactivate automatic neq elimination
    noneq_elim,!.
ssolve_command(noneq_elim) :- !,
    assertz(noneq_elim).

ssolve_command(ran_elim) :- !,       %% (re-)activate automatic ran elimination
    cond_retract(noran_elim).
ssolve_command(noran_elim) :-        %% deactivate automatic ran elimination
    noran_elim,!.
ssolve_command(noran_elim) :- !,
    assertz(noran_elim).

ssolve_command(comp_elim) :- !,      %% (re-)activate automatic comp elimination
    cond_retract(nocomp_elim).
ssolve_command(nocomp_elim) :-       %% deactivate automatic comp elimination
    nocomp_elim,!.
ssolve_command(nocomp_elim) :- !,
    assertz(nocomp_elim).

ssolve_command(irules) :- !,         %% (re-)activate automatic application of inference rules
    cond_retract(noirules).
ssolve_command(noirules) :-          %% deactivate automatic application of inference rules
    noirules,!.
ssolve_command(noirules) :- !,
    assertz(noirules).

ssolve_command(strategy(Str)) :- !,  %% change goal atom selection strategy
    retract(strategy(_)),
    assertz(strategy(Str)).

ssolve_command(int_solver(Slv)) :-   %% get the current integer arithmetic solver (clpfd|clpq)
    var(Slv),!,
    b_getval(int_solver,Slv).
ssolve_command(int_solver(Slv)) :-!, %% change the current integer arithmetic solver (clpfd|clpq)
    (Slv == clpq -> true; Slv == clpfd),
    b_setval(int_solver,Slv).

ssolve_command(nofinal) :- !,        %% deactivate final mode for constraint solving
    cond_retract(final).
ssolve_command(final) :- !,          %% activate final mode for constraint solving
    set_final.

ssolve_command(mode(M)) :-           %% get the current constraint solving mode 
    var(M),!,
    b_getval(smode,M).
ssolve_command(mode(M)) :- !,        %% change the constraint solving mode 
    (  M == solver -> 
          b_setval(smode,M)
    ; 
       M == prover -> 
          default_prover_mode_strategies(S),           
          b_setval(smode,prover(S))
    ;
       M = prover(Lst), 
       prover_mode_strategies(Lst),
       b_setval(smode,M)    
    ).

ssolve_command(nofix_size) :- !,     %% deactivate fixed set cardinality mode for constraint solving
    b_setval(fix_size,off).
ssolve_command(fix_size) :- !,       %% activate fixed set cardinality mode for constraint solving
    b_setval(fix_size,on).

% activation of groundsol implies activation of fix_size
% same for nogroundsol
ssolve_command(nogroundsol) :- !,     %% deactivate ground solutions for constraint solving
    b_setval(groundsol,off),
    b_setval(fix_size,off).
ssolve_command(groundsol) :- !,       %% activate ground solutions for constraint solving
    b_setval(groundsol,on),
    b_setval(fix_size,on).

ssolve_command(noshow_min) :- !,     %% deactivate fixed set cardinality mode for constraint solving
    b_setval(show_min,off).
ssolve_command(show_min) :- !,       %% activate fixed set cardinality mode for constraint solving
    b_setval(show_min,on).

ssolve_command(notype_check) :- !,   %% deactivate type-checking
    b_setval(type_check,off).
ssolve_command(type_check) :- !,     %% activate type-checking
    (\+type_checker ->
        throw(setlog_excpt('no type-checker loaded'))
    ;
        b_setval(type_check,on)
    ).

ssolve_command(vcg(Spec)) :- !,      %% reads file Spec, check some consistency conditions
    (\+vcg ->                        %% and generates the corresponding vc's..
         throw(setlog_excpt('no VC generator loaded'))
    ;
     vcg(Spec)
    ).



%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% Standard Prolog built-in predicates

sys(nl,0) :- !.   
sys(ground,1) :- !.   
sys(var,1) :- !.   
sys(nonvar,1) :- !.   
sys(name,2) :- !.   
sys(functor,3) :- !.   
sys(arg,3) :- !.   
sys(=..,2) :- !.   
sys(==,2) :- !.   
sys(\==,2) :- !.   
sys(@<,2) :- !.   
sys(@>,2) :- !.   
sys(@=<,2) :- !.   
sys(@>=,2) :- !.   
%%********* list to be completed!!*********


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% Redefined Prolog built-in predicates 

sys_special(write(_)) :- !.           
sys_special(read(_)) :- !.            
sys_special(assert(_)) :- !.   
sys_special(consult_lib) :- !.   
sys_special(add_lib(_)) :- !.        
sys_special(consult(_)) :- !.     
sys_special(consult(_,_)) :- !.   
sys_special(labeling(_)) :- !.   
sys_special(listing) :- !.        
sys_special(abolish) :- !.   
sys_special(help) :- !.   
sys_special(h(_)) :- !.   
sys_special(halt) :- !.             
sys_special(time(_,_)) :- !.           

ssolve_special(write(T),[]) :-             %% write
    !,postproc(T,NewT),
    write(NewT).

ssolve_special(read(T),C) :-               %% read
    !,setlog_read(Tout),
    preproc(Tout,T,C).

ssolve_special(assert(Clause),[]) :-       %% assert
    !,setassert(Clause).

ssolve_special(consult_lib,[]) :-          %% stores clauses contained in the {log} library file into
    !,rem_clause(lib), rem_clause(tmp(lib)),       %% the current program in the library ctxt
    setlog_open('setloglib.slog',read,FileStream), %% (removing all clauses possibly stored
    switch_ctxt(lib,OldCtxt),                      %% in the same ctxt)
    read_loop_np(FileStream),
    switch_ctxt(OldCtxt,_),
    close(FileStream).

ssolve_special(add_lib(File),[]) :-        %% adds clauses contained in file F to the current
    !, setlog_open(File,read,FileStream),          %% program in the library ctxt (without
    switch_ctxt(lib,OldCtxt),                      %% removing existing clauses)
    read_loop_np(FileStream),
    switch_ctxt(OldCtxt,_),
    close(FileStream).

ssolve_special(consult(File),[]) :-        %% stores clauses contained in file F into
    !, setlog_open(File,read,FileStream),          %% the current program in the user ctxt
    write('consulting file '), write(File),        %% (removing all clauses possibly stored
    write(' ...'), nl,                             %% in the same ctxt)
    ssolve_special(abolish,_),
    read_loop(FileStream,1),
    write('file '), write(File), write(' consulted.'), nl,
    close(FileStream).

ssolve_special(consult(File,Mode),[]) :-
    !,
    (Mode==mute ->                         %% consult using mute mode
         setlog_open(File,read,FileStream),
         ssolve_special(abolish,_),
         read_loop_np(FileStream),
         close(FileStream)
     ;
     Mode==app ->                          %% consult using app mode
         setlog_open(File,read,FileStream),
         write('consulting file '), write(File),
         write(' ...'), nl,
         read_loop(FileStream,1),
         write('file '), write(File), write(' consulted.'), nl,
         close(FileStream)
     ;
         throw(setlog_excpt('invalid argument'))
     ).

ssolve_special(labeling(X),[]) :-          %% explicit labeling for integer variables
    nonvar(X),!.
ssolve_special(labeling(X),[]) :- !,
    labeling(X).

ssolve_special(listing,[]) :-              %% listing
    !,nl, list_all.

ssolve_special(abolish,[]) :-              %% abolish
    !,rem_clause(usr),
    rem_clause(tmp(usr)).

ssolve_special(help,[]) :- !, h(setlog).   %% help
ssolve_special(h(X),[]) :- !, h(X).

ssolve_special(halt,[]) :-                 %% halt
    abort.

ssolve_special(time(G,T),C) :-             %% time
    statistics(runtime,_),
    write('STARTING ...'),nl,
    solve_goal_fin(G,C),!,
    write('END'),nl,
    statistics(runtime,[_,T]).
ssolve_special(time(_G,T),_C) :-           %% time
    write('END'),nl,
    statistics(runtime,[_,T]).
                                         
%%%%%%%%%%%% auxiliary predicates for sys_special/2

setlog_read(Term) :-
    catch(read(Term),Msg,syntax_error_msg(Msg)).

setlog_open(File,Mode,Stream) :-
    mk_file_name(File,FullName),
    catch(open(FullName,Mode,Stream),Msg,existence_error_msg(Msg)).

mk_file_name(F,FullName) :-
    path(Dir),
    name(Dir,DirList),
    name(F,FList),
    append(DirList,FList,FullNameList),
    name(FullName,FullNameList).

existence_error_msg(_Text) :-
    throw(setlog_excpt('file does not exist')).

rem_clause(Ctxt) :-
    retract(isetlog(_,Ctxt)),
    fail.
rem_clause(_).


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%% Negation %%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

naf_negate(A,[]) :-                 %% Negation as Failure
    (   ground(A) ->
        \+ solve_goal_fin(A,_)
    ;
        naf_negate_warning(A,_)
    ).

naf_negate_warning(A,_) :-  
    solve_goal_fin(A,_),!,
    print_single_warning('***WARNING***: using unsafe negation'),
    fail.
naf_negate_warning(_,_).

print_single_warning(Msg) :-
    \+ nowarning,
    !,
    nl, write(Msg), nl,
    assertz(nowarning).
print_single_warning(_). 
              
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

c_negate(A,ClistNew) :-             %% Simplified Constructive Negation
    chvar([],L1,A,[],L1new,B),
    constrlist(B,Clist,Alist),
    solve_goal_fin_constr(Clist,Alist,Clist0),
    final_sat(Clist0,Clist1),!,
    dis(L1,L1new,Dis),
    append(Clist1,Dis,CC),
    neg_solve(CC,ClistNew,L1).
c_negate(_A,[]).

neg_solve([],[],_) :- !, fail.
neg_solve(Clist,ClistNew,LVars) :-
    neg_constr_l(Clist,ClistNew,LVars).

neg_constr_l([],_,_) :- !,fail.
neg_constr_l(Clist,ClistNew,LVars) :-
    member(C,Clist),
    neg_constr(C,ClistNew,LVars).

neg_constr(A nin B,[A in B],_) :- !.
neg_constr(A neq B,[],LVars) :- !,
    extract_vars(B,V),
    subset_strong(V,LVars),
    sunify(A,B,_).
neg_constr(A = B,[A neq B],LVars) :-
    extract_vars(B,V),
    subset_strong(V,LVars),!.
neg_constr(_A = _B,_,_) :-
    print_single_warning('***WARNING***: unsupported form of negation').

dis([],[],[]) :-!.
dis([X|L1],[Y|L2],[X=Y|L3]) :-
    nonvar(Y),!,
    dis(L1,L2,L3).
dis([X|L1],[Y|L2],[X=Y|L3]) :-
    var(Y),
    member_strong(Y,L2),!,
    dis(L1,L2,L3).
dis([X|L1],[Y|L2],L3) :-
    X=Y,
    dis(L1,L2,L3).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

negate(true,false) :- !.            %% Defined negation    
negate(false,true) :- !.
negate(A = B,A neq B) :- !.
negate(A neq B,A = B) :- !.
negate(A in B,A nin B) :- !.
negate(A nin B,A in B) :- !.

negate(A >= B,A < B) :- !.
negate(A > B,A =< B) :- !.
negate(A =< B,A > B) :- !.
negate(A < B,A >= B) :- !.
negate(A is B,(N is B & A neq N)) :- !.
negate(A =:= B,(N1 is A & N2 is B & N1 neq N2)) :- !.
negate(A =\= B,(N1 is A & N2 is B & N1 = N2)) :- !.

negate(subset(A,B),nsubset(A,B)) :- !.
negate(nsubset(A,B),subset(A,B)) :- !.
negate(disj(A,B),ndisj(A,B)) :- !.
negate(ndisj(A,B),disj(A,B)) :- !.
negate(un(A,B,C),nun(A,B,C)) :- !.
negate(nun(A,B,C),un(A,B,C)) :- !.
negate(inters(A,B,C),ninters(A,B,C)) :- !.
negate(ninters(A,B,C),inters(A,B,C)) :- !.
negate(diff(A,B,C),ndiff(A,B,C)) :- !.
negate(ndiff(A,B,C),diff(A,B,C)) :- !.
negate(size(A,N),nsize(A,N)) :- !.
negate(nsize(A,N),size(A,N)) :- !.

negate(set(A),nset(A)) :- !.
negate(nset(A),set(A)) :- !.
negate(integer(A),ninteger(A)) :- !.
negate(ninteger(A),integer(A)) :- !.
negate(pair(A),npair(A)) :- !.
negate(npair(A),pair(A)) :- !.
negate(pfun(A),npfun(A)) :- !.
negate(npfun(A),pfun(A)) :- !.
negate(rel(A),nrel(A)) :- !.
negate(nrel(A),rel(A)) :- !.

negate(dom(A,B),ndom(A,B)) :- !.
negate(ndom(A,B),dom(A,B)) :- !.
negate(ran(A,B),nran(A,B)) :- !.
negate(nran(A,B),ran(A,B)) :- !.
negate(inv(A,B),ninv(A,B)) :- !.
negate(ninv(A,B),inv(A,B)) :- !.
negate(id(A,B),nid(A,B)) :- !.
negate(nid(A,B),id(A,B)) :- !.
negate(comp(A,B,C),ncomp(A,B,C)) :- !.
negate(ncomp(A,B,C),comp(A,B,C)) :- !.
negate(dres(A,B,C),ndres(A,B,C)) :- !.
negate(ndres(A,B,C),dres(A,B,C)) :- !.
negate(dares(A,B,C),ndares(A,B,C)) :- !.
negate(ndares(A,B,C),dares(A,B,C)) :- !.
negate(rres(A,B,C),nrres(A,B,C)) :- !.
negate(nrres(A,B,C),rres(A,B,C)) :- !.
negate(rares(A,B,C),nrares(A,B,C)) :- !.
negate(nrares(A,B,C),rares(A,B,C)) :- !.
negate(rimg(A,B,C),nrimg(A,B,C)) :- !.
negate(nrimg(A,B,C),rimg(A,B,C)) :- !.
negate(oplus(A,B,C),noplus(A,B,C)) :- !.
negate(noplus(A,B,C),oplus(A,B,C)) :- !.

negate(apply(A,B,C),napply(A,B,C)) :- !.
negate(napply(A,B,C),apply(A,B,C)) :- !.
negate(dompf(A,B),ndompf(A,B)) :- !.
negate(ndompf(A,B),dompf(A,B)) :- !.

negate(foreach(D,P,F,FP),nforeach(D,P,F,FP)) :- !.
negate(nforeach(D,P,F,FP),foreach(D,P,F,FP)) :- !.
negate(exists(D,F),nexists(D,F)) :- !.  
negate(nexists(D,F),exists(D,F)) :- !.
negate(exists(D,P,F,FP),nexists(D,P,F,FP)) :- !.
negate(nexists(D,P,F,FP),exists(D,P,F,FP)) :- !.

negate(let(V,B,F),nlet(V,B,F)) :-!.
negate(nlet(V,B,F),let(V,B,F)) :-!.

negate(dec(_,_),false) :- !.

negate(neg(A),A) :- !.  
negate(implies(A,B),nimplies(A,B)) :- !.  
negate(nimplies(A,B),implies(A,B)) :- !.     

negate((B1 & true),NB1) :- !,
    negate(B1,NB1).
negate((B1 & B2),(NB1 or NB2)) :- !,
    negate(B1,NB1),
    negate(B2,NB2).
negate((B1 or B2),(NB1 & NB2)) :- !,
    negate(B1,NB1),
    negate(B2,NB2).

negate(A,NegA) :-                       % user-defined predicates, with user-defined negative counterparts
   nonvar(A), functor(A,F,N),           % check if the negation of A is present; otherwise use the next clause
   name(F,FCodeList),
   (FCodeList = [110,95|RFCodeList] ->  % if prefix "n_"  
    name(NegF,RFCodeList)               % remove prefix "n_"
   ;
    name(NegF,[110,95|FCodeList])       % add prefix "n_"
   ),
   functor(AGen,NegF,N),
   isetlog((AGen :- _B),_),!,
   A =.. [F|Args],
   NegA =.. [NegF|Args].
negate(A, (naf A)).                     % user-defined predicates, without user-defined negative counterparts

% Returns the preconditions, and their negations, of a conjunction of functional predicates
% Pos is the conjunction of the preconditions of each functional predicate
% Neg is the disjunction of the negation of the preconditions of each functional predicate
%
get_preconditions(FifthArg,Pos,Neg) :-
    get_preconditions1(FifthArg,true,false,Pos,Neg).
%   remove_false(Neg1,Neg).  %to remuve useless 'false' in Neg: e.g., P or false or Q or R or false...

get_preconditions1((FifthArg & FifthArgRest),IPos,INeg,FPos,FNeg) :-
    preconditions(FifthArg,NegPre,PosPre),!,
    conj_append(PosPre,IPos,Pos1),
    Neg1 = (INeg or NegPre),
    get_preconditions1(FifthArgRest,Pos1,Neg1,FPos,FNeg).
get_preconditions1(FifthArg,IPos,INeg,FPos,FNeg) :-
    preconditions(FifthArg,NegPre,PosPre),!,
    conj_append(PosPre,IPos,FPos),
    FNeg = (INeg or NegPre).

% preconditions(+FP,-Neg,-Pos):
% returns the negation of the preconditions (Neg) of a functional predicate (FP)
% and the conjunction of its preconditions (Pos)
% (in apply, the positive precondition is simply 'true' because apply generates
% the precondition by itself. I.e., apply(F,X,Y) => pfun(F) & comp({[X,X]},F,{H}))
%
preconditions(apply(F,X,_Y), 
    (npfun(F) or comp({} with [X,X],F,{})), true) :-!.    %i.e., X nin dom(F)
preconditions(_Z is _X mod Y, 
    Y = 0, Y neq 0) :-!.
preconditions(applyTo(F,X,_Y), 
    comp({} with [X,X],F,{}), true) :- !. %\+nopfcheck,!.     %i.e., X nin dom(F) 
preconditions(_,false,true).
%TO BE COMPLETED


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%% Intensional sets and RUQs processing %%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% Intensional sets

solve_SF(S,GName,PName,VarList,Cin,Cout) :-
    b_getval(smode,Current),
    b_setval(smode,solver),
    solve_SF_cont(S,GName,PName,VarList,Cin,Cout),
    b_setval(smode,Current).
solve_SF_cont(S,_GName,PName,VarList,Cin,Cout) :-
    nonvar(S), S = {},!,
    InPred =.. [PName,{}|VarList],
    solve_goal_fin_constr(Cin,[cneg(InPred & true)],Cout).
    % print_warning_SF(VarList).
solve_SF_cont({},_GName,PName,VarList,Cin,Cout) :-
    InPred =.. [PName,{}|VarList],
    solve_goal_fin_constr(Cin,[cneg(InPred & true)],Cout).
    % print_warning_SF(VarList).
solve_SF_cont(S,GName,_PName,VarList,_Cin,Cout) :-
    InPred =.. [GName,X|VarList],
    setof(X,solve_goal_fin(InPred,C1),L),
    list_to_set(L,S,C2),
    append(C2,C1,Cout).
    % print_warning_SF(VarList).

%print_warning_SF(VarList) :-      % uncomment to check possibly unsafe uses of intensional sets
%   \+ ground(VarList),!,
%   print_single_warning('***WARNING***: uninstantiated free variable in intensional set').


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% RUQs

solve_RUQ(S,InName,VarList,Cin,Cout) :-
    b_getval(smode,Current),
    b_setval(smode,solver),
    solve_RUQ_cont(S,InName,VarList,Cin,Cout),
    b_setval(smode,Current).
solve_RUQ_cont(S,_,_,C,C) :-
    nonvar(S),
    empty_aggr(S),!.
solve_RUQ_cont(S,InName,VarList,Cin,Cout) :-
    nonvar(S), S = int(L,H),!,                         % solve RUQ's over intervals
    force_bounds_values(L,H,IntC),
    solve_RUQ_int(int(L,H),InName,VarList,Cin,Cout1),
    append(IntC,Cout1,Cout).
solve_RUQ_cont(S,InName,VarList,Cin,Cout) :-           % over a given aggregate
    nonvar(S),!,
    aggr_comps(S,X,R),
    InPred =.. [InName,X|VarList],
    solve_goal_fin_constr(Cin,[InPred],C2),
    solve_RUQ_cont(R,InName,VarList,C2,Cout).
solve_RUQ_cont(S,_,_,C,C) :-
    var(S), S = {}.
solve_RUQ_cont(S,InName,VarList,Cin,Cout) :-           % over an unspecified aggregate
    var(S), S = R with X,
    InPred =.. [InName,X|VarList],
    solve_goal_fin_constr([X nin R|Cin],[InPred],C2),
    solve_RUQ_cont(R,InName,VarList,C2,Cout),
    aggr_ordered(S).

solve_RUQ_int(int(L,L),InName,VarList,Cin,Cout) :- !,
    InPred =.. [InName,L|VarList],    % forall(X in int(L,L),InName(X,VarList))
    solve_goal_fin_constr(Cin,[InPred],Cout).
solve_RUQ_int(int(L,H),InName,VarList,Cin,Cout) :-
    InPred =.. [InName,L|VarList],    % forall(X in int(L,H),InName(X,VarList))
    solve_goal_fin_constr(Cin,[InPred],C2),
    L1 is L + 1,
    solve_RUQ_cont(int(L1,H),InName,VarList,C2,Cout).

%%%%%%%%%%%%%% auxiliary predicates for solve_RUQ/5

aggr_ordered(S) :- var(S),!.
aggr_ordered({}) :- !.
aggr_ordered(S) :-
    S = R with X,
    in_order(X,R),
    aggr_ordered(R).

in_order(_A,S) :- var(S),!.
in_order(_A,{}) :- !.
in_order(A,S) :-
    S = _R with _B,
    var(A), !.
in_order(A,S) :-
    S = R with B,
    var(B), in_order(A,R),!.
in_order(A,S) :-
    S = _R with B,
    A @=< B.

force_bounds_values(A,B,IntC) :-
    solve_int(A =< B,IntC),
    (var(A) -> labeling(A) ; true),
    (var(B) -> labeling(B) ; true).


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%                              %%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%% Program storing and printing %%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%                              %%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%      Load additional components    %%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%%%%%%%%%%%%%%%%%%%% load the advanced size solver 

load_size_solver :-
    size_solver_file(Size_solver_file),
    mk_file_name(Size_solver_file,FullName),
    (exists_file(FullName) ->
        consult(FullName),
        assertz(size_solver_on)
    ;
        cond_retract(size_solver_on),    
        write('No advanced size solver loaded (file '''),
        write(Size_solver_file), write(''')'), nl
    ).

%%%%%%%%%%%%%%%%%%%% load filtering rules %%%%%%%%%%%%%%%%%%%%%

load_rwrules_lib :-
    rw_rules(Filtering_rules_file),
    mk_file_name(Filtering_rules_file,FullName),
    (exists_file(FullName) ->
        consult(FullName),
        (filter_on -> true ; assertz(filter_on))
    ;                                                       
        cond_retract(filter_on),    
        write('No filtering rules loaded (file '''),
        write(Filtering_rules_file), write(''')'), nl
    ).

%%%%%%%%%%%%%%%%%%%% load the type checker %%%%%%%%%%%%%%%%%%%%%

load_type_checker :-
    type_checker_file(F),
    mk_file_name(F,FullName),
    (exists_file(FullName) ->
        consult(FullName),
        assertz(type_checker)
    ;
        cond_retract(type_checker),    
        write('No type-checker loaded (file '''),
        write(F), write(''')'), nl
    ).

%%%%%%%% load the verification condition generator %%%%%%%%%%%%%

load_vcg :-
    vcg_file(F),
    mk_file_name(F,FullName),
    (exists_file(FullName) ->
        consult(FullName),
        assertz(vcg)
    ;
        cond_retract(vcg),    
        write('No VC generator loaded (file '''),
        write(F), write(''')'), nl
    ).


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%   Consulting and storing {log} clauses
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

ctx(usr).

read_loop_np(FileStream) :-
    setlog_read(FileStream,Clause),
    Clause \== end_of_file,
    !,
    assert_or_solve(Clause),
    read_loop_np(FileStream).
read_loop_np(_).

read_loop(FileStream,N) :-
    setlog_read(FileStream,Clause),
    Clause \== end_of_file,
    !,
    assert_or_solve(Clause,N),
    N1 is N + 1,
    read_loop(FileStream,N1).
read_loop(_,_).

setlog_read(Stream,Term) :-
    \+type_checker,!, 
    nb_setval(err,false),                          
    setlog_read_term(Stream,Term,[]).
setlog_read(Stream,Term) :-
    nb_setval(err,false),
    (b_getval(type_check,on) ->            
        %catch(setlog_read_term(Stream,G,[variable_names(VarNames)]),Msg,syntax_error_cont_msg(Msg)),
        setlog_read_term(Stream,G,[variable_names(VarNames)]),
        (nb_getval(err,false) -> 
           (G = (:- Goal) ->
                catch(typecheck(G,VarNames),setlog_excpt(Msg),excpt_action(Msg)),
                ignore_type_dec(Goal,Term)    
           ;
            G = (H :- Goal) ->
                catch(typecheck(G,VarNames),setlog_excpt(Msg),excpt_action(Msg)),
                Term = (H :- Goal)
           ;                          %G = H (unit clause)
                catch(typecheck((G :- true),VarNames),setlog_excpt(Msg),excpt_action(Msg)),   
                Term = G
           ) 
        ; 
         true
        )
    ;
        %catch(setlog_read_term(Stream,G,[]),Msg,syntax_error_cont_msg(Msg)),
        setlog_read_term(Stream,G,[]),
        (nb_getval(err,false) ->
           (G = (:- Goal) ->
              ignore_type_dec(Goal,Term)             
           ;
              Term = G
           ) 
        ; 
         true
        )
    ).    

setlog_read_term(Stream,Term,Options) :-
    catch(read_term(Stream,Term,[singletons(SVars)|Options]),Msg,syntax_error_cont_msg(Msg)),
    (nb_getval(err,false) ->
      (
       var(SVars) -> true
       ;
       SVars == [] -> true
       ;
       (warnings(on) -> 
          write('***WARNING***: singleton variables '), write(SVars), write(' in clause '),nl,
          write(Term),nl
        ; 
        true
       )
      ) 
      ; 
       true
     ).

assert_or_solve((:- Goal)) :-
    %solve(Goal,_),!.   
    catch(solve(Goal,_),setlog_excpt(Msg),excpt_action(Msg)),!.  
assert_or_solve((:- Goal)) :-!,
    write('***WARNING***: goal (directive) failed: '), write(Goal), nl.
assert_or_solve(Clause) :-
    setassert(Clause).

assert_or_solve((:- Goal),_) :-
    %solve(Goal,_),!.   
    catch(solve(Goal,_),setlog_excpt(Msg),excpt_action(Msg)),!.  
assert_or_solve((:- Goal),_) :- !,
    write('***WARNING***: goal (directive) failed: '), write(Goal), nl.
assert_or_solve(Clause,N) :-
    setassert(Clause),
    write('Clause '), write(N), write(' stored'), nl.

setassert(Clause) :-
    ctx(Ctxt),
    setassert(Clause,Ctxt).
setassert(Clause,_) :-       
    clause_head(Clause,H),
    predefined_pred(H),!,
    write('***WARNING***: attempt to redefine system predicate '), write(H), nl.
setassert(Clause,Ctxt) :-
    transform_clause(Clause,BaseClause),
    assertz(isetlog(BaseClause,Ctxt)).

switch_ctxt(NewCtxt,OldCtxt) :-
    retract(ctx(OldCtxt)),
    assertz(ctx(NewCtxt)).

tmp_switch_ctxt(OldCtxt) :-
    ctx(OldCtxt),
    functor(OldCtxt,tmp,_),!.
tmp_switch_ctxt(OldCtxt) :-
    retract(ctx(OldCtxt)),
    NewCtxt = tmp(OldCtxt),
    assertz(ctx(NewCtxt)).

syntax_error_cont_msg(Text) :-
    write('Syntax error: '), write(Text), nl,
    nb_setval(err,true).
  
clause_head((H :- _Body),H) :- !.    
clause_head(H,H).
  
predefined_pred(A) :-
    (atomic_constr(A),!
    ;
     isetlog((A :- _B),sys),!
    ;
     meta_pred(A),!
    ;
     setlog_command(A),!
    ;
     sys_special(A),!
    ;
     functor(A,F,N),
     sys(F,N),!
    ).


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%   Program listing
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

list_all :-
    isetlog((H :- B),usr),
    postproc(H,Hnew), write(Hnew),
    write_body(B).
list_all.

write_body(true) :-
    !, write('.'),nl,nl,
    fail.
write_body(C & true) :-
    type_constr(C),!, write('.'),nl,nl,
    fail.
write_body(B) :-
    write((:-)), nl,
    write('   '), postproc(B,Bnew), write_atoms(Bnew), write('.'),nl,nl,
    fail.

write_atoms(B & true) :-
    !, write_atom(B).
write_atoms(B1 & B2) :-
    write_atom(B1),
    (   B2 = (C & _), type_constr(C) ->
        true
    ;
        write(' & '), nl, write('   ')
    ),
    write_atoms(B2).

write_atom(A) :-
    var(A),!,
    write(A).
write_atom(ruq_call(Aggr,Goal_name,FV)) :-
    !,
    write('forall('),write(X),write(' in '),write(Aggr),write(','),
    RUQ_body_pred =.. [Goal_name,X|FV], isetlog((RUQ_body_pred :- RUQ_body),_),
    extract_vars(RUQ_body,Vars),
    remove_list([X|FV],Vars,LocalVars),
    postproc(RUQ_body,RUQ_bodyNew),
    (   LocalVars = [] ->
        write_atoms(RUQ_bodyNew), write(')')
    ;
        write('exists('),write(LocalVars),write(','),
        write_atoms(RUQ_bodyNew), write('))')
    ).
write_atom(C) :-
    type_constr(C), !.
%write_atom(neg A) :- !,
%    write('neg '),
%    write('('), write_atoms(A), write(')').
write_atom(naf A) :- !,
    write('naf '),
    write('('), write_atoms(A), write(')').
write_atom(call(A)) :- !,
    write(call),
    write('('), write_atoms(A), write(')').
write_atom(call(A,C)) :- !,
    write(call),
    write('('), write_atoms(A),write(','),write(C),write(')').
write_atom(solve(A)) :- !,
    write(solve),
    write('('), write_atoms(A), write(')').
write_atom((A)!) :- !,
    write('('),
    write_atoms(A),
    write(')!').
write_atom(delay(A,G)) :- !,
    write(delay),write('('),
    write_atoms(A),write(','),
    write_atoms(G),
    write(')').
write_atom((A1 or A2)) :- !,
    write('('), write_atoms(A1),
    write(' or '),
    write_atoms(A2), write(')').
write_atom(B) :-
    write(B).


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%                              %%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%% The {log] Constraint Solver  %%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%                              %%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% Exported predicates:
%
%             atomic_constr/1,
%             sat/3,
%             final_sat/2,
%             sunify/3,
%
%             solve_int/1
%             add_intv/2,
%             labeling/1,
%             is_int_var/1
%             check_int_constr/2
%             finalize_int_constr/1

%%%%%%%%%%%%%%%%%%% Atomic constraints %%%%%%%%%%%%%%%%%%%%%%

atomic_constr(_ nin _) :-!.
atomic_constr(_ in _) :-!.
atomic_constr(_ neq _) :-!.
atomic_constr(_ = _) :-!.
atomic_constr(set(_)) :-!.
atomic_constr(integer(_)) :-!.
atomic_constr(un(_,_,_)) :-!.
atomic_constr(subset(_,_)) :-!.
atomic_constr(disj(_,_)) :-!.
atomic_constr(inters(_,_,_)) :-!.
atomic_constr(ssubset(_,_)) :-!.
atomic_constr(diff(_,_,_)) :-!.

atomic_constr(delay(_,_)) :-!.
atomic_constr(solved(_,_,_)) :-!.     % for internal use only
atomic_constr(glb_state(_)) :-!.      % for internal use only
atomic_constr(dec(_,_)) :-!.    

atomic_constr(size(_,_)) :-!.
atomic_constr(sum(_,_)) :-!.
atomic_constr(smin(_,_)) :-!.
atomic_constr(smax(_,_)) :-!.

%atomic_constr(bag(_)) :-!.
%atomic_constr(list(_)) :-!.

atomic_constr(_ is _) :-!.
atomic_constr(_ =< _) :-!.
atomic_constr(_ < _) :-!.
atomic_constr(_ >= _) :-!.
atomic_constr(_ > _) :-!.

atomic_constr(pfun(_)) :-!.
atomic_constr(rel(_)) :-!.
atomic_constr(pair(_)) :-!.
atomic_constr(dom(_,_)) :-!.
atomic_constr(inv(_,_)) :-!.
atomic_constr(id(_,_)) :-!.
atomic_constr(ran(_,_)) :-!.
atomic_constr(comp(_,_,_)) :-!.
atomic_constr(dompf(_,_)).
atomic_constr(comppf(_,_,_)) :-!.
atomic_constr(apply(_,_,_)) :-!.
atomic_constr(dres(_,_,_)) :-!.
atomic_constr(drespf(_,_,_)) :-!.
atomic_constr(rres(_,_,_)) :-!.
atomic_constr(dares(_,_,_)) :-!.
atomic_constr(rares(_,_,_)) :-!.
atomic_constr(oplus(_,_,_)) :-!.

atomic_constr(nset(_)) :-!.
atomic_constr(ninteger(_)) :-!.
atomic_constr(npair(_)) :-!.
atomic_constr(npfun(_)) :-!.
atomic_constr(nrel(_)) :-!.

atomic_constr(nun(_,_,_)) :-!.
atomic_constr(ndisj(_,_)) :-!.
atomic_constr(ndom(_,_)) :-!.
atomic_constr(ninv(_,_)) :-!.
atomic_constr(ncomp(_,_,_)) :-!.

atomic_constr(nran(_,_)) :-!.
atomic_constr(ndres(_,_,_)) :-!.
atomic_constr(ndares(_,_,_)) :-!.
atomic_constr(nrres(_,_,_)) :-!.
atomic_constr(nrares(_,_,_)) :-!.
atomic_constr(napply(_,_,_)) :-!.
atomic_constr(nrimg(_,_,_)) :-!.
atomic_constr(noplus(_,_,_)) :-!.
atomic_constr(nid(_,_)) :-!.
atomic_constr(ndompf(_,_)) :-!.

atomic_constr(foreach(_,_)) :-!.      % foreach(C in D,G) or foreach(X,G)   
atomic_constr(foreach(_,_,_,_)) :-!.  % foreach(C in D,[V1,...,Vn],G,FP)
atomic_constr(nforeach(_,_)) :-!.
atomic_constr(nforeach(_,_,_,_)) :-!.
atomic_constr(exists(_,_)) :-!.       % exists(C in D,G) or exists(X,G)    
atomic_constr(exists(_,_,_,_)) :-!.   % exists(C in D,[V1,...,Vn],G,FP)
atomic_constr(nexists(_,_)) :-!.
atomic_constr(nexists(_,_,_,_)) :-!.

atomic_constr(let(_,_,_)) :-!.        % let(Vars,Conj,F)  
atomic_constr(nlet(_,_,_)) :-!.       % nlet(Vars,Conj,F)  


%%%%%%%%%%%%  Constraint solver main procedure %%%%%%%%%%%%

%%%% sat(+Constraint,-Solved_Form_Constraint,+final/non-final)
sat(C,SFC,F) :-
    %norep_in_list(C,NewC),
    norep_in_list_split(C,NewC,_,Nsize),

    (size_solver_on, Nsize >= 1 ->       
       b_setval(using_size_solver,true)  
    ;
       true
    ), 
    sat1(NewC,SFC,F).

sat1([],[],_) :-!.
sat1(C,SFC,F) :-
    trace_in(C,1),
    sat_step(C,NewC,R,F),
    sat_cont(R,NewC,SFC,F).

sat_cont(R,NewC,SFC,F) :-                   %if R=='stop', then no rule has changed the CS in the last
    R == stop,!,                            %call to 'sat_step' (-> fixpoint); otherwise, call 'sat' again
    trace_out(NewC,1),
    norep_in_list_split(NewC,RedC,RedCS,Nsize),   %remove possibly repeated constraints in the CS
    trace_in(RedC,2),                       %and split the CS into <neq-constraints,other-constraints>
    (size_solver_on ->
        cond_check_size(RedC,Nsize,MinSol),
        %DBG write('cond_check_size '),write(MinSol),nl,  
        b_setval(minsol,MinSol)
    ;
        true
    ),
    global_check1(RedC,RedCS,RevC1,F),      %rewrite RedC to RevC
    global_check2(RevC1,RedCS,RevC,F),      %rewrite RedC to RevC
    (RevC == RedC ->
        SFC=RevC,     %if RedC==RevC, then no rewriting has been applied:
        trace_out(NewC,2)
    ;                                       %RevC is the resulting constraint;
        sat1(RevC,SFC,F)                    %otherwise, call 'sat' again
    ).
sat_cont(_R,NewC,SFC,F) :-
    sat1(NewC,SFC,F).

%%%%%%%%%%%%%%%%%% auxiliary predicates for the constraint solver %%%%%%%%%%%%%%%%%%%

%norep_in_list_split(+C,-RedC,-CS,-Nsize)   %true if C is the current constraint store, RedC is C without
                                            %duplicate constraints, CS is RedC splitted in two lists, 
                                            %NSize is the number of size constraints in C
norep_in_list_split([],[],cs([],[]),0) :-!.
norep_in_list_split([A|R],S,CS,Nsize) :-    %remove duplicate elements
    member_strong(A,R),!,
    norep_in_list_split(R,S,CS,Nsize).
norep_in_list_split([A|R],[A|S],cs([A|NeqCS],OtherCS),Nsize) :-   %move neq constraint to 1st list of CS
    A = (_ neq _),!,
    norep_in_list_split(R,S,cs(NeqCS,OtherCS),Nsize).
norep_in_list_split([A|R],[A|S],cs([A|NeqCS],OtherCS),Nsize) :-   %move type constraint to 1st list of CS
    type_constr(A),!,
    norep_in_list_split(R,S,cs(NeqCS,OtherCS),Nsize).
norep_in_list_split([A|R],[A|S],cs([A|NeqCS],OtherCS),Nsize) :-   %move glb_state constraint to 1st list of CS
    A = glb_state(_),!,
    norep_in_list_split(R,S,cs(NeqCS,OtherCS),Nsize).
norep_in_list_split([A|R],[A|S],cs(NeqCS,[A|OtherCS]),Nsize) :-   %count size constraints
    is_size(A,_,_,_),!,
    norep_in_list_split(R,S,cs(NeqCS,OtherCS),Nsize1),
    Nsize is Nsize1+1.
norep_in_list_split([A|R],[A|S],cs(NeqCS,[A|OtherCS]),Nsize) :-   %move all other constraints to 2nd list of CS
    norep_in_list_split(R,S,cs(NeqCS,OtherCS),Nsize).

split_cs([],cs([],[])) :-!.                  %split the CS into <neq-constraints,other-constraints>
split_cs([A|R],cs([A|NeqCS],OtherCS)) :-     %(called by filter_and_check)
    (A = (_ neq _) ->
        true
    ;
     type_constr(A) ->
        true
    ;
        A = glb_state(_)
    ),
    !,
    split_cs(R,cs(NeqCS,OtherCS)).
split_cs([A|R],cs(NeqCS,[A|OtherCS])) :-
    split_cs(R,cs(NeqCS,OtherCS)).

compute_sols :-                         
    b_getval(smode,solver),!.    
compute_sols :-   
    b_getval(using_size_solver,true),!.   
 
%%%%%%%%%%%%%%%%%%%% constraint solving tracing

trace_in(C,L) :-
    trace(sat),
    !,
    write('>>> Entering Level '), write(L),nl,
    write('>>> Input constraint: '), write(C), nl,
    write('Press return to continue '), nl,
    get_code(_).
trace_in(_,_).

trace_out(_C,L) :-
    trace(sat),
    !,
    write('<<< Level '), write(L), write(' fixed point reached'),nl,
    %DBG write('<<< Output constraint: '), write(C),nl,
    nl.
trace_out(_,_).

trace_irules(Rule) :-
    trace(irules),
    !,
    write('\n>>> Using inference rule '), write(Rule),nl.
trace_irules(_).

trace_firules(Rule) :-
    trace(irules),
    !,
    write('\n>>> Using filtering inference rule '), write(Rule),nl.
trace_firules(_).

trace_ffrules(Rule) :-
    trace(irules),
    !,
    write('\n>>> Using filtering fail rule '), write(Rule),nl.
trace_ffrules(_).


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% sat_step %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%sat_step(InC,_OutC,_Stop,_F) :-   %only for debugging purposes
%   write('    >>>>> sat step: '), write(InC),nl,
%   get_code(_),
%   fail.

sat_step([],[],stop,_F) :- !.
sat_step([C1|R1],R2,Z,F) :-
    sat_step(C1,[C1|R1],R2,Z,F).

%%%%%%%%%%%%%             % global state constraints (for internal use only)
sat_step(glb_state(Rel),[glb_state(Rel)|R1],R2,Stop,F) :- 
    (ground(Rel) ->                      %remove unuseful glb_state constraints from the CS          
        true                             %e.g. 2 < 4
    ;
     Rel =.. [_OP,E1,E2], E1 == E2 ->    %e.g. X =< X
        true
    ;
        Rel =.. [is,E1,E2], 
        ground(E1), term_variables(E2,[_])
    ),                                  
    !,
    sat_step(R1,R2,Stop,F).
sat_step(glb_state(Rel),[glb_state(Rel)|R1],[glb_state(Rel)|R2],Stop,F) :-
    !,
    sat_step(R1,R2,Stop,F).

%%%%%%%%%%%%%             % type declaration constraints
sat_step(dec(X,T),[dec(X,T)|R1],[dec(X,T)|R2],Stop,F) :-    
    !,
    sat_step(R1,R2,Stop,F).
%%%%%%%%%%%%%             % equality/inequality constraints
sat_step(_ neq _,C,R2,Z,F) :- !,
    sat_neq(C,R2,Z,F).
sat_step(_ = _,C,R2,Z,F) :- !,
    sat_eq(C,R2,Z,F).
%%%%%%%%%%%%%             % membership/not membership constraints
sat_step(_ nin _,C,R2,Z,F) :- !,
    sat_nin(C,R2,Z,F).
sat_step(_ in _,C,R2,Z,F) :- !,
    sat_in(C,R2,Z,F).
%%%%%%%%%%%%%             % set/interval positive constraints
sat_step(un(X,Y,W),[un(X,Y,W)|R1],R2,Z,F) :- !,
    sat_un([un(X,Y,W)|R1],R2,Z,F).
sat_step(subset(X,Y),[subset(X,Y)|R1],R2,Z,F) :- !,
    sat_sub([subset(X,Y)|R1],R2,Z,F).
sat_step(ssubset(X,Y),[ssubset(X,Y)|R1],R2,Z,F) :- !,
    sat_ssub([ssubset(X,Y)|R1],R2,Z,F).
sat_step(inters(X,Y,W),[inters(X,Y,W)|R1],R2,Z,F) :- !,
    sat_inters([inters(X,Y,W)|R1],R2,Z,F).
sat_step(disj(X,Y),[disj(X,Y)|R1],R2,Z,F) :- !,
    sat_disj([disj(X,Y)|R1],R2,Z,F).
sat_step(diff(X,Y,W),[diff(X,Y,W)|R1],R2,Z,F) :- !,
    sat_diff([diff(X,Y,W)|R1],R2,Z,F).
%%%%%%%%%%%%%             % aggregate constraints
sat_step(size(X,Y),[size(X,Y)|R1],R2,Z,F) :- !,
    sat_size([size(X,Y)|R1],R2,Z,F).
sat_step(sum(X,Y),[sum(X,Y)|R1],R2,Z,F) :- !,
    sat_sum([sum(X,Y)|R1],R2,Z,F).
sat_step(smin(X,Y),[smin(X,Y)|R1],R2,Z,F) :- !,
    sat_min([smin(X,Y)|R1],R2,Z,F).
sat_step(smax(X,Y),[smax(X,Y)|R1],R2,Z,F) :- !,
    sat_max([smax(X,Y)|R1],R2,Z,F).
%%%%%%%%%%%%%             % set/interval negative constraints
sat_step(nun(X,Y,W),[nun(X,Y,W)|R1],R2,Z,F) :- !,
    sat_nun([nun(X,Y,W)|R1],R2,Z,F).
sat_step(ndisj(X,Y),[ndisj(X,Y)|R1],R2,Z,F) :- !,
    sat_ndisj([ndisj(X,Y)|R1],R2,Z,F).
%%%%%%%%%%%%%             % type constraints
sat_step(set(X),[set(X)|R1],R2,Z,F) :- !,
    sat_set([set(X)|R1],R2,Z,F).
sat_step(integer(X),[integer(X)|R1],R2,Z,F) :-!,
    sat_integer([integer(X)|R1],R2,Z,F).
sat_step(pair(X),[pair(X)|R1],R2,Z,F) :- !,
    sat_pair([pair(X)|R1],R2,Z,F).
%sat_step(bag(X),[bag(X)|R1],R2,Z,F) :- !,
%    sat_bag([bag(X)|R1],R2,Z,F).
%sat_step(list(X),[list(X)|R1],R2,Z,F) :- !,
%    sat_list([list(X)|R1],R2,Z,F).
sat_step(nset(X),[nset(X)|R1],R2,Z,F) :- !,
    sat_nset([nset(X)|R1],R2,Z,F).
sat_step(ninteger(X),[ninteger(X)|R1],R2,Z,F) :-!,
    sat_ninteger([ninteger(X)|R1],R2,Z,F).
sat_step(npair(X),[npair(X)|R1],R2,Z,F) :- !,
    sat_npair([npair(X)|R1],R2,Z,F).
%%%%%%%%%%%%%             % control constraints
sat_step(delay(A,G),[delay(A,G)|R1],R2,Z,F) :- !,
    sat_delay([delay(A,G)|R1],R2,Z,F).
sat_step(solved(C,G,Lev),[solved(C,G,Lev)|R1],R2,Z,F) :- !,   % "solved" constraints: used to avoid
    sat_solved([solved(C,G,Lev)|R1],R2,Z,F).                  % repeated additions of the same constraints
%%%%%%%%%%%%%             % arithmetic constraints
sat_step(X is Y,[X is Y|R1],R2,Z,F) :-                  % RIS equality (with RIS "expansion")
    nonvar(Y),Y = {},!,
    sat_step([X = {}|R1],R2,Z,F).
sat_step(X is Y,[X is Y|R1],R2,Z,F) :-                  % RIS equality (with RIS "expansion")
    nonvar(Y),Y = _ with _,!,
    sat_step([X = Y|R1],R2,Z,F).
sat_step(X is Y,[X is Y|R1],R2,Z,F) :-                  % RIS equality (with RIS "expansion")
    ris_term(Y,Ris),!,
    expandable_ris(Ris),
    sat_riseq([X is Y|R1],R2,Z,F).
sat_step(X is Y,[X is Y|R1],R2,Z,F) :- !,               % integer equality (with expression evaluation)
    sat_eeq([X is Y|R1],R2,Z,F).
sat_step(_ =< _,C,R2,Z,F) :- !,                         % integer comparison relations
    sat_crel(C,R2,Z,F).
sat_step(_ < _,C,R2,Z,F) :- !,                          % integer comparison relations
    sat_crel(C,R2,Z,F).
sat_step(_ >= _,C,R2,Z,F) :- !,                         % integer comparison relations
    sat_crel(C,R2,Z,F).
sat_step(_ > _,C,R2,Z,F) :- !,                          % integer comparison relations
    sat_crel(C,R2,Z,F).
%%%%%%%%%%%%%             % binary relation and partial function positive constraints
sat_step(rel(X),[rel(X)|R1],R2,Z,F) :- !,
    sat_rel([rel(X)|R1],R2,Z,F).
sat_step(pfun(X),[pfun(X)|R1],R2,Z,F) :- !,
    sat_pfun([pfun(X)|R1],R2,Z,F).
sat_step(dom(X,Y),[dom(X,Y)|R1],R2,Z,F) :- !,
    sat_dom([dom(X,Y)|R1],R2,Z,F).
sat_step(ran(X,Y),[ran(X,Y)|R1],R2,Z,F) :- !,
    sat_ran([ran(X,Y)|R1],R2,Z,F).
sat_step(comp(R,S,T),[comp(R,S,T)|R1],R2,Z,F) :- !,
    sat_comp([comp(R,S,T)|R1],R2,Z,F).
sat_step(inv(X,Y),[inv(X,Y)|R1],R2,Z,F) :- !,
    sat_inv([inv(X,Y)|R1],R2,Z,F).
sat_step(id(X,Y),[id(X,Y)|R1],R2,Z,F) :- !,
    sat_id([id(X,Y)|R1],R2,Z,F).
sat_step(dompf(R,A),[dompf(R,A)|R1],R2,Z,F) :- !,
    sat_dompf([dompf(R,A)|R1],R2,Z,F).
sat_step(comppf(R,S,T),[comppf(R,S,T)|R1],R2,Z,F) :- !,
    sat_comppf([comppf(R,S,T)|R1],R2,Z,F).
sat_step(dres(A,R,S),[dres(A,R,S)|R1],R2,Z,F) :- !,
    sat_dres([dres(A,R,S)|R1],R2,Z,F).
sat_step(drespf(A,R,S),[drespf(A,R,S)|R1],R2,Z,F) :- !,
    sat_drespf([drespf(A,R,S)|R1],R2,Z,F).
sat_step(rres(R,A,S),[rres(R,A,S)|R1],R2,Z,F) :- !,
    sat_rres([rres(R,A,S)|R1],R2,Z,F).
sat_step(dares(A,R,S),[dares(A,R,S)|R1],R2,Z,F) :- !,
    sat_dares([dares(A,R,S)|R1],R2,Z,F).
sat_step(rares(R,A,S),[rares(R,A,S)|R1],R2,Z,F) :- !,
    sat_rares([rares(R,A,S)|R1],R2,Z,F).
sat_step(apply(S,X,Y),[apply(S,X,Y)|R1],R2,Z,F) :- !,
    sat_apply([apply(S,X,Y)|R1],R2,Z,F).
sat_step(oplus(S,R,T),[oplus(S,R,T)|R1],R2,Z,F) :- !,
    sat_oplus([oplus(S,R,T)|R1],R2,Z,F).
%%%%%%%%%%%%%             % binary relation and partial function negative constraints
sat_step(npfun(X),[npfun(X)|R1],R2,Z,F) :- !,
    sat_npfun([npfun(X)|R1],R2,Z,F).
sat_step(nrel(X),[nrel(X)|R1],R2,Z,F) :- !,
    sat_nrel([nrel(X)|R1],R2,Z,F).
sat_step(ndom(R,A),[ndom(R,A)|R1],R2,Z,F) :- !,
    sat_ndom([ndom(R,A)|R1],R2,Z,F).
sat_step(ninv(R,S),[ninv(R,S)|R1],R2,Z,F) :- !,
    sat_ninv([ninv(R,S)|R1],R2,Z,F).
sat_step(ncomp(R,S,T),[ncomp(R,S,T)|R1],R2,Z,F) :- !,
    sat_ncomp([ncomp(R,S,T)|R1],R2,Z,F).
sat_step(nran(R,A),[nran(R,A)|R1],R2,Z,F) :- !,
    sat_nran([nran(R,A)|R1],R2,Z,F).
sat_step(ndres(A,R,S),[ndres(A,R,S)|R1],R2,Z,F) :- !,
    sat_ndres([ndres(A,R,S)|R1],R2,Z,F).
%
sat_step(ndares(A,R,S),[ndares(A,R,S)|R1],R2,Z,F) :- !,
    sat_ndares([ndares(A,R,S)|R1],R2,Z,F).
sat_step(nrres(R,A,S),[nrres(R,A,S)|R1],R2,Z,F) :- !,
    sat_nrres([nrres(R,A,S)|R1],R2,Z,F).
sat_step(nrares(R,A,S),[nrares(R,A,S)|R1],R2,Z,F) :- !,
    sat_nrares([nrares(R,A,S)|R1],R2,Z,F).
sat_step(napply(S,X,Y),[napply(S,X,Y)|R1],R2,Z,F) :- !,
    sat_napply([napply(S,X,Y)|R1],R2,Z,F).
sat_step(nrimg(R,A,B),[nrimg(R,A,B)|R1],R2,Z,F) :- !,
    sat_nrimg([nrimg(R,A,B)|R1],R2,Z,F).
sat_step(noplus(A,R,S),[noplus(A,R,S)|R1],R2,Z,F) :- !,
    sat_noplus([noplus(A,R,S)|R1],R2,Z,F).
sat_step(nid(X,Y),[nid(X,Y)|R1],R2,Z,F) :- !,
    sat_nid([nid(X,Y)|R1],R2,Z,F).
sat_step(ndompf(R,A),[ndompf(R,A)|R1],R2,Z,F) :- !,
    sat_ndompf([ndompf(R,A)|R1],R2,Z,F).
%%%%%%%%%%%%%             % foreach and nforeach, exists and nexists
sat_step(foreach(_,_,_,_),[foreach(D,P,Fo,FP)|R1],R2,Z,F) :- !,
    sat_foreach4([foreach(D,P,Fo,FP)|R1],R2,Z,F).
sat_step(nforeach(_,_,_,_),[nforeach(D,P,Fo,FP)|R1],R2,Z,F) :- !,
    sat_nforeach4([nforeach(D,P,Fo,FP)|R1],R2,Z,F).
sat_step(exists(_,_),[exists(D,Fo)|R1],R2,Z,F) :- !,
    sat_exists([exists(D,Fo)|R1],R2,Z,F).
sat_step(nexists(_,_),[nexists(D,Fo)|R1],R2,Z,F) :- !,
    sat_nexists([nexists(D,Fo)|R1],R2,Z,F).
sat_step(exists(_,_,_,_),[exists(D,P,Fo,FP)|R1],R2,Z,F) :- !,
    sat_exists4([exists(D,P,Fo,FP)|R1],R2,Z,F).
sat_step(nexists(_,_,_,_),[nexists(D,P,Fo,FP)|R1],R2,Z,F) :- !,
    sat_nexists4([nexists(D,P,Fo,FP)|R1],R2,Z,F).
sat_step(foreach(_,_),[foreach(V,Fo)|R1],R2,Z,F) :- !,   
    sat_foreach2([foreach(V,Fo)|R1],R2,Z,F).
sat_step(nforeach(_,_),[nforeach(V,Fo)|R1],R2,Z,F) :- !,      
    sat_nforeach2([nforeach(V,Fo)|R1],R2,Z,F).

sat_step(let(_,_,_),[let(V,B,Frm)|R1],R2,Z,F) :- !,   
    sat_let([let(V,B,Frm)|R1],R2,Z,F).
sat_step(nlet(_,_,_),[nlet(V,B,Frm)|R1],R2,Z,F) :- !,   
    sat_nlet([nlet(V,B,Frm)|R1],R2,Z,F).


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%      Level 1     %%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%%%%%%%%%%%%
%%%%%%%%%%%% Rewriting rules for general constraints (=, neq) %%%%%%%%%%%%%
%%%%%%%%%%%%

%%%%%%%%%%%%%%%%%%%%%% equality (=/2)

%sat_eq([T1 = T2|R1],[T1 = T2|R2],Stop,nf) :-       % int(A,B) = {} --> delayed until final_sat is called
%    nonvar(T1), T1 = int(A,B), var(A), var(B),
%    nonvar(T2), is_empty(T2),!,
%    sat_step(R1,R2,Stop,nf).
%sat_eq([T1 = T2|R1],[T2 = T1|R2],Stop,nf) :-       % {} = int(A,B)  --> delayed until final_sat is called
%    nonvar(T2), T2 = int(A,B), var(A), var(B),
%    nonvar(T1), is_empty(T1),!,
%    sat_step(R1,R2,Stop,nf).

sat_eq([T1 = T2|R1],R2,R,F) :-                      % ris = t or t = ris
    (ris_term(T1) ->
        true
    ;
        ris_term(T2)
    ),
    !,
    sat_eq_ris([T1 = T2|R1],R2,R,F).
sat_eq([T1 = T2|R1],R2,R,F) :-                      % cp = t or t = cp
    (   nonvar(T1), T1 = cp(_,_) ->
        true
    ;
        nonvar(T2), T2 = cp(_,_)
    ),
    !,
    sat_eq_cp([T1 = T2|R1],R2,R,F).
sat_eq([T1 = T2|R1],R2,c,F) :-                      % t1 = t2 (t1, t2 not ris-term)
    sunify(T1,T2,C),
    append(C,R1,R3),
    sat_step(R3,R2,_,F).

%%%%%%%%%%% equality involving RIS

sat_eq_ris([T1 = T2|R1],R2,c,F) :-                  % ris(...) = ris(...), identical ris
    %write('0-'),
    T1 == T2,!,
    %write(rule('identical ris')),nl,
    sat_step(R1,R2,_,F).
sat_eq_ris([T1 = T2|R1],R2,c,F) :-                  % ris(Z in D,...) = X  (var-ris D, var X)
    %write('1-'),
    var(T2),
    ris_term(T1,ris(_ in Dom,_,_,_,_)), var_ris(Dom),
    occur_check(T2,T1),!,
    %write(rule('ris(var)=var')),nl,
    T2 = T1,
    sat_step(R1,R2,_,F).

sat_eq_ris([T1 = T2|R1],[T1 = T2|R2],Stop,F) :-     % ris(Z in X,...)=X or ris(Z in D,t[X]...)=X  (var-ris D, var X) --> irreducible
    %write('2-'),
    var(T2),
    ris_term(T1,ris(_CtrlExpr in Dom,_,_,_P,_)), var_ris(Dom),
    %write(rule('ris(X)=X')),nl,
    sat_step(R1,R2,Stop,F).

sat_eq_ris([T1 = T2|R1],R2,c,F) :-                  % X = ris(...) --> ris(...) = X   (var X)
    %write('3-'),
    var(T1),!,
    %write(rule('X=ris-->ris=X')),nl,
    sat_eq_ris([T2 = T1|R1],R2,_,F).
sat_eq_ris([T1 = T2|R1],R2,c,F) :-                  % t = ris(...) (t not ris-term) ---> ris(...) = t
    %write('4-'),
    nonvar(T1),\+ris_term(T1),!,
    %write(rule('t=ris-->ris=t')),nl,
    sat_eq_ris([T2 = T1|R1],R2,_,F).

sat_eq_ris([T1 = T2|R1],R2,c,F) :-                  % ris(X in {},...) = T (T any term, including another RIS)
    %write('5-'),
    nonvar(T1), is_empty(T1),!,
    %write(rule('ris({})=t')),nl,
    sunify(T2,{},C), append(C,R1,R3),
    sat_step(R3,R2,_,F).

sat_eq_ris([T1 = E|R1],[T1 = E|R2],Stop,F) :-       % ris(V in D,F,P) = {}   (var-ris D) --> irreducible
    %write('6-'),
    ris_term(T1,ris(_ in Dom,_,_,_,_)), var_ris(Dom),
    nonvar(E), is_empty(E),!,
    %write(rule('ris(var)={}')),nl,
    sat_step(R1,R2,Stop,F).
sat_eq_ris([T1 = T2|R1],[T1 = T2|R2],Stop,F) :-     % ris(X in int(A,B),...) = T (int(A,B) open interval --> irreducible)
    %write('7-'),
    ris_term(T1,ris(_ in Dom,_,_,_,_)),
    open_intv(Dom),!,
    %write(rule('ris(int(A,B))=t')),nl,
    sat_step(R1,R2,Stop,F).

sat_eq_ris([T1 = E |R1],R2,c,F) :-                  % ris(V,{...},F,P) = {}   (nonvar-ris D)
    %write('8-'),
    ris_term(T1,ris(CE_Dom,V,Fl,P,PP)),
    nonvar(E), is_empty(E),
    nonvar(CE_Dom), CE_Dom = (CtrlExpr in Dom), nonvar_ris(Dom),!,
    %write(rule('ris(d)={}')),nl,
    ctrl_expr(CtrlExpr,V,LV,CtrlExprNew),
    (sat_step([Dom = {}|R1],R2,_,F)
    ;
      get_rest(Dom,CtrlExprNew,D,CNS),
      (nonvar(CNS) ->
        append(CNS,R1,R3),
        %
        chvar(LV,[],_FVars,[Fl,P,PP,CtrlExpr],[],_FVarsNew,[FlNew,_PNew,PPNew,CtrlExprNew]),
        %%%%find_corr_list(CtrlExpr,CtrlExprNew,FVars,FVarsNew),
        negate(FlNew,NegFl),
        get_preconditions(PPNew,PosPre,NegPre),
        conj_append(PosPre,PPNew,PrePPNew),
        conj_append(PrePPNew,NegFl,PreNegFl),
        mk_atomic_constraint((PreNegFl or NegPre),NegFlD),
        %
        sat_step([NegFlD,ris(CtrlExpr in D,V,Fl,P,PP) = E|R3],R2,_,F)
      ;
        sat_step([ris(CtrlExpr in D,V,Fl,P,PP) = E|R1],R2,_,F)   % to discard domain elements that 
      )                                                          % don't match ther control term
    ).

sat_eq_ris([T1 = S|R1],[T1 = S|R2],Stop,F) :-  % ris(X in D,...) = int(A,B) (open interval --> irreducible)
    %write('9-'),
    nonvar(S), open_intv(S),!,
    %write(rule('ris=int(A,B)')),nl,
    sat_step(R1,R2,Stop,F).

sat_eq_ris([T1 = S |R1],R2,c,F) :-    % ris(V,{...},F,P)={...} or ris(V,{...},F,P)=S (var S), or ris(V,{...},F,P)=ris(...)
    %write('10-'),
    ris_term(T1,ris(CE_Dom,V,Fl,P,PP)),
    nonvar(CE_Dom), CE_Dom = (CtrlExpr in Dom), nonvar_ris(Dom),!,
    %write(rule('ris(d)={...} OR ris(d)=var')),nl,
    ctrl_expr(CtrlExpr,V,LV,CtrlExprNew),
    get_rest(Dom,CtrlExprNew,D,CNS),
    (nonvar(CNS),!,
     append(CNS,R1,R3),
     chvar(LV,[],_FVars,[Fl,P,PP,CtrlExpr],[],_FVarsNew,[FlNew,PNew,PPNew,CtrlExprNew]),
     %%%%%find_corr_list(CtrlExpr,CtrlExprNew,FVars,FVarsNew),
     get_preconditions(PPNew,PosPre,NegPre),
     (
      solve_expression(Z,PNew),
      mk_atomic_constraint(PPNew,PPNewD),
      conj_append(PosPre,FlNew,PreFlNew),
      mk_atomic_constraint(PreFlNew,FlNewD),
      %
      sat_step([FlNewD,PPNewD,ris(CtrlExpr in D,V,Fl,P,PP) with Z = S |R3],R2,_,F)
     ;
      negate(FlNew,NegFl),
      conj_append(PosPre,PPNew,PrePPNew),
      conj_append(PrePPNew,NegFl,PreNegFl),
      mk_atomic_constraint((PreNegFl or NegPre),NegFlD),
      %
      sat_step([NegFlD,ris(CtrlExpr in D,V,Fl,P,PP) = S |R3],R2,_,F)
     )
    ;
     sat_step([ris(CtrlExpr in D,V,Fl,P,PP) = S |R1],R2,_,F)
    ).

sat_eq_ris([T1 = S|R1],R2,c,F) :-     % ris(V,D,F,P) = {.../ris(W,D,G,Q)}  (var-ris D)  % non-admissible constraints
    %write('11-nonadmissible'),
    ris_term(T1,ris(CE_Dom1,_,_,P1,_)),
    nonvar(CE_Dom1), CE_Dom1 = (CtrlExpr1 in Dom1), var_ris(Dom1),
    nonvar(S), set_int(S),tail2(S,TS),
    tail(TS,TTS),
    samevar(Dom1,TTS),
    (var(TS), CtrlExpr1 \== P1 ->
        true
    ;
     ris_term(TS,ris(CE_Dom2,_,_,P2,_)),
     nonvar(CE_Dom2), CE_Dom2 = (CtrlExpr2 in _Dom2),
     CtrlExpr1 == P1, CtrlExpr2 \== P2 ->
        true
    ;
        ris_term(TS,ris(CE_Dom2,_,_,P2,_)),
        nonvar(CE_Dom2), CE_Dom2 = (CtrlExpr2 in _Dom2),
        CtrlExpr1 \== P1, CtrlExpr2 == P2
    ),
    !,
    (final ->
        throw(setlog_excpt('non-admissible constraint'))
    ;
        sat_step([delay(T1 = S,false)|R1],R2,_,F)
    ).

sat_eq_ris([T1 = S|R1],R2,c,F) :-      % ris(V,D,F,P) = {.../D}   (var-ris D)   % special case, simple RIS
    %write('11-'),
    ris_term(T1,ris(CE_Dom,V,Fl,P,PP)),
    nonvar(CE_Dom), CE_Dom = (CtrlExpr in Dom), var_ris(Dom),
    nonvar(S), set_int(S), tail2(S,TS),
    %
    CtrlExpr == P,
    samevarris_simple2(Dom,TS),!,
    %write(rule('ris(X)={_/X}')),nl,
    %
    first_rest(S,X,A,CNS), append(CNS,R1,R3),
    replace_tail(A,N,NewA),
    ctrl_expr(CtrlExpr,V,LV,CtrlExprNew),
    %
    chvar(LV,[],_Vars,[Fl,P,PP,CtrlExpr],[],_VarsNew,[FlNew,PNew,PPNew,CtrlExprNew]),
    %%%%%find_corr_list(CtrlExpr,CtrlExprNew,Vars,VarsNew),
    get_preconditions(PPNew,PosPre,_),
    %
    solve_expression(Z,PNew),
    mk_atomic_constraint(PPNew,PPNewD),
    conj_append(PosPre,FlNew,PreFlNew),
    mk_atomic_constraint(PreFlNew,FlNewD),
    %
    Z = X,
    sat_step([FlNewD,PPNewD, Dom=N with CtrlExprNew, ris(CtrlExpr in N,V,Fl,P,PP)=NewA |R3],R2,_,F).

sat_eq_ris([T1 = S|R1],R2,c,F) :-      % ris(V,D,F,P) = {.../ris(W,D,G,Q)}  (var-ris D)  % special case, non-simple RIS
    %write('11BIS-'),
    ris_term(T1,ris(CE_Dom,V,Fl,P,PP)),
    nonvar(CE_Dom), CE_Dom = (CtrlExpr in Dom), var_ris(Dom),
    %
    nonvar(S), set_int(S), tail2(S,TS_RIS),
    ris_term(TS_RIS,ris(CE_Dom2,V2,Fl2,P2,PP2)),
    nonvar(CE_Dom2), CE_Dom2 = (CtrlExpr2 in _Dom2),
    CtrlExpr \== P, CtrlExpr2 \== P2,
    tail(TS_RIS,TDom),
    samevar(Dom,TDom),!,
    %write(rule('ris(X)={_/X}, control term neq pattern')),nl,
    %
    first_rest(S,X,A,CNS), append(CNS,R1,R3),
    replace_tail(A,N,NewA),
    %%% gamma(n)  & Z=v(n) & X=Z  (n is CtrlExprNew)
    ctrl_expr(CtrlExpr,V,LV,CtrlExprNew),
    %
    chvar(LV,[],_Vars,[Fl,P,PP,CtrlExpr],[],_VarsNew,[FlNew,PNew,PPNew,CtrlExprNew]),
    %%%%%find_corr_list(CtrlExpr,CtrlExprNew,Vars,VarsNew),
    get_preconditions(PPNew,PosPre,_),
    %
    solve_expression(Z,PNew),
    mk_atomic_constraint(PPNew,PPNewD),
    conj_append(PosPre,FlNew,PreFlNew),
    mk_atomic_constraint(PreFlNew,FlNewD),
    %
    Z = X,
    %
    %%% not phi(n')  or Z2=u(n') & X=Z2    (n' is CtrlExpr2New and n = n')
    ctrl_expr(CtrlExpr2,V2,LV2,CtrlExpr2New),
    %
    chvar(LV2,[],_Vars2,[Fl2,P2,PP2,CtrlExpr2],[],_Vars2New,[Fl2New,P2New,PP2New,CtrlExpr2New]),
    %%%%%%find_corr_list(CtrlExpr2,CtrlExpr2New,Vars2,Vars2New),
    get_preconditions(PP2New,PosPre2,NegPre2),
    CtrlExprNew=CtrlExpr2New,        % n' must be the same as n
    %
    (   solve_expression(Z2,P2New),
        mk_atomic_constraint(PP2New,PP2NewD),
        Z2 = X,
        sat_step([FlNewD,PPNewD,PP2NewD,Dom=N with CtrlExprNew,ris(CtrlExpr in N,V,Fl,P,PP)=NewA |R3],R2,_,F)
    ;   %%% not phi(n)
        negate(Fl2New,NegFl),
        conj_append(PosPre2,PP2New,PrePP2New),
        conj_append(PrePP2New,NegFl,PreNegFl2),
        mk_atomic_constraint((PreNegFl2 or NegPre2),NegFlD2),
        sat_step([FlNewD,PPNewD,NegFlD2, Dom=N with CtrlExpr2New, ris(CtrlExpr in N,V,Fl,P,PP)=NewA |R3],R2,_,F)  
    ).

sat_eq_ris([T1 = S|R1],R2,c,F) :-         % ris(V,D,F,P) = {...}   (var-ris D)
    %write('12-'),
    ris_term(T1,ris(CE_Dom,V,Fl,P,PP)),
    nonvar(S), set_int(S),
    nonvar(CE_Dom), CE_Dom = (CtrlExpr in Dom), var_ris(Dom),!,
    %write(rule('ris(var)={...}')),nl,get(_),
    first_rest(S,X,A,CNS), append(CNS,R1,R3),
    ctrl_expr(CtrlExpr,V,LV,CtrlExprNew),
    %
    chvar(LV,[],_Vars,[Fl,P,PP,CtrlExpr],[],_VarsNew,[FlNew,PNew,PPNew,CtrlExprNew]),
    %%%%%find_corr_list(CtrlExpr,CtrlExprNew,Vars,VarsNew),
    get_preconditions(PPNew,PosPre,_),
    %
    solve_expression(Z,PNew),
    mk_atomic_constraint(PPNew,PPNewD),
    conj_append(PosPre,FlNew,PreFlNew),
    mk_atomic_constraint(PreFlNew,FlNewD),
    %
    Z = X,
    sat_step([FlNewD, PPNewD, Dom=D with CtrlExprNew | R3], R2aux, _, F),
    sat_step([ris(CtrlExpr in D,V,Fl,P,PP)=A |R2aux], R2, _, F).

sat_eq_ris([T2 = T1 |R1],R2,c,F) :-        % ris(V2,D2,F2,P2)=ris(V1,D1,F1,P1)  (nonvar-ris D1, var-ris D2)
    %write('14-'),
    ris_term(T1,ris(_ in Dom1,_,_,_,_)),
    ris_term(T2,ris(_ in Dom2,_,_,_,_)),
    nonvar_ris(Dom1), %%%first_rest(Dom1,_,_,_),
    var_ris(Dom2),!,
    %write(rule('ris(var)=ris(d) --> ris(d)=ris(var)')),nl,
    sat_eq_ris([T1 = T2|R1],R2,_,F).

sat_eq_ris([T1 = T2|R1],[T1 = T2|R2],Stop,F) :-      % ris(V1,D1,F1,P1)=ris(V2,D2,F2,P2)  (var-ris D1, var-ris D2) --> irreducible
    %write('16-'),
    ris_term(T1,ris(_ in Dom1,_,_,_,_)),
    ris_term(T2,ris(_ in Dom2,_,_,_,_)),
    var_ris(Dom1), var_ris(Dom2),!,
    %write(rule('ris(var)=ris(var)')),nl,
    sat_step(R1,R2,Stop,F).

samevarris_simple2(R,S) :-                 % R and S are the same var.
    var(S),!,
    samevar(R,S).
samevarris_simple2(R,S) :-                 % R is a var and S is a simple-RIS ris(C in {.../R},F,C)
    ris_term(S,ris(CtrlExpr in Dom,_,_,P,_)), %var_ris(Dom),
    CtrlExpr == P,                         % counterexample:  ris(Z in X,Z=Z) = {a/ris(V in {b/X},V=V)}.
    tail(Dom,TDom),
    samevar(R,TDom).

% RIS expansion:
% S is ris(X in D,F,P), D var-ris or ground set: S collects all values satisfying the RIS
%
sat_riseq([X is RIS|R1],[X is RIS|R2],Stop,nf) :-    % X is ris(...Dom...), var-ris Dom
    ris_term(RIS,ris(_ in Dom,_,_,_,_)),             % delayed until final_sat is called
    var_ris(Dom),!,
    sat_step(R1,R2,Stop,nf).
sat_riseq([X is RIS|R1],R2,c,f) :-                   % collecting all values satisfying the RIS (final mode only)
    ris_term(RIS,ris(_ in Dom,_,_,_,_)),
    var_ris(Dom),!,
    sunify(X,RIS,C), append(C,R1,R3),                % X = RIS,
    sat_step(R3,R2,_,f).
sat_riseq([X is RIS|R1],R2,c,F) :-                   % collecting all values satisfying the RIS
    b_getval(smode,Mode),
    b_setval(smode,solver),
    final_sat([RIS = R with A, A nin R, set(R)],C1),
    append(C1,R1,C1R1), dsunify(X,RR with A,C2),     % X = RR with A
    append(C2,C1R1,R3),
    sat_riseq_notemptyset(R,RR,R2,R3,F),
    b_setval(smode,Mode).
sat_riseq([X is RIS|R1],R2,c,F) :-
    final_sat([RIS = {}],C), %!,
    append(C,R1,R3),
    is_empty(X),                                     % X = {}
    sat_step(R3,R2,_,F).

% deterministic sunify
dsunify(T1,T2,C) :-
    sunify(T1,T2,C),!.

sat_riseq_notemptyset(R,RR,R2,R3,F) :-
    (var(R) ->
        RR=R, sat_step(R3,R2,_,F)
    ;
     ris_term(R) ->
        sat_step([RR is R,set(RR)|R3],R2,_,F)
    ;
     is_empty(R) ->
        RR={}, sat_step(R3,R2,_,F)
    ;
        tail2(R,T), nonvar(T), \+ris_term(T), !,
        RR=R, sat_step(R3,R2,_,F)
    ).

%%%% auxiliary predicates for dealing with RIS

ris_term(T) :-
    nonvar(T),
    T = ris(_,_,_,_,_).

ris_term(T,ris(CE_Dom,LVars,Fl,P,PP)) :-
    nonvar(T),
    T = ris(CE_Dom,LVars,Fl,P,PP).

var_ris(D) :-       % var_ris(D): true if D is the domain of a variable-RIS
    var(D),
    !.
var_ris(D) :-    
    ris_term(D,ris(_ in Dom,_,_,_,_)),
    open_intv(Dom),!.   
var_ris(D) :-       
    ris_term(D,ris(_ in Dom,_,_,_,_)),
    var_ris(Dom).

nonvar_ris(Ris) :-
    nonvar(Ris), \+ris_term(Ris),!.
nonvar_ris(Ris) :-
    ris_term(Ris,ris(_ in Dom,_,_,_,_)),!,
    nonvar_ris(Dom).

%ex. solve_expression(X,2+3)  --> X = 5.
%ex. solve_expression(X,2+Y)  --> clpfd: 2+Y#=X, 2+Y#=_ or clpq: {X=2+Y, _=2+Y}
%ex. solve_expression(X,f(Y)) --> X = f(Y).
%
solve_expression(X,E) :-
    nonvar(E),
    test_integer_expr(E),
    !,
    solve_int(X is E,_).
solve_expression(X,E) :-
    X = E.

% expandable_ris(r): true if r is a RIS whose domain D is either a var-RIS or
% a ground set (i.e., {}, or {t1,...,tn} with t1,...,tn ground, or a closed interval,
% or cp(a,b) with a,b ground)
%
expandable_ris(ris(CE_Dom,_,_Fl,_P,_PP)) :-
    (   nonvar(CE_Dom), CE_Dom = (_ in Dom), ground_elems(Dom) ->
        true
    ;
        throw(setlog_excpt('arguments are not sufficiently instantiated'))
    ).

% ground_elems(r): true if r is either a variable ris, or {}, or {t1,...,tn/X} with
% t1,...,tn ground and ground_elems(X), or a closed interval, or cp(a,b) with a,b ground,
% or a RIS with ground_elems(Dom))
%
ground_elems(R) :-
    var_ris(R),!.
ground_elems(R) :-
    closed_intv(R,_,_),!.
ground_elems({}) :- !.
ground_elems(R with A) :- !,
    ground(A), ground_elems(R).
ground_elems(cp(A,B)) :- !,
    ground(A), ground(B).
ground_elems(Ris) :-
    ris_term(Ris,ris(_ in Dom,_,_,_,_)),!,
    ground_elems(Dom).
                                               
ctrl_expr(X0,V,[X0|V],_X) :-                    %ctrl_expr(+CT,+VList,-NewVList,-NewCT)
    var(X0),!.                                  %CT can be either X, or [X|R], or R with X, X,Y,R vars,
ctrl_expr([X0|Y0],V,[X0,Y0|V],[_X|_Y]) :-       %or any nested closed list of variables, without repetitions (e.g.,[[X,Y],W,[Q,[T,R]]])
    var(X0),var(Y0),!.                          %NewVList is the list of vars in CT + vars in VList
ctrl_expr(Y0 with X0,V,[X0,Y0|V],_Y with _X) :- %NewCT is CT with all its variable renamed
    var(X0), var(Y0),!.                         %e.g., ctrl_expr([X|Y],[Z],NewVList,NewCT) --> NewVList=[X,Y,Z], NewCT=[N1|N2]
ctrl_expr(CT,VList,NewVList,NewCT) :-
    CT \== [],
    closed_list(CT,VList,NewVList,NewCT),!.
ctrl_expr(_CT,_VList,_NewVList,_NewCT) :-       %otherwise
    %throw(setlog_excpt('non-admissible control term in RIS')).    
    throw(setlog_excpt('wrong control term')).    

closed_list(L,_,_,_) :-
   var(L),!,fail.
closed_list([],Vars,Vars,[]) :-!.
closed_list([X|R],Vars,NewVars,[_X|NewR]) :-
   var(X),
   \+member_strong(X,Vars),!,
   closed_list(R,[X|Vars],NewVars,NewR).
closed_list([T|R],Vars,NewVars,[NewT|NewR]) :-
   closed_list(T,Vars,TVars,NewT),
   closed_list(R,TVars,NewVars,NewR).

%get_rest(+S,?X,-R,-C)
get_rest(S,X,R,C) :-                  % same as first_rest(S,X,R,C)  OR
    first_rest(S,X,R,C),!.            % S is a set and X is not its first component,
get_rest(R with _,_,R,_).             % R is S without its first component and C is an unbound var.

mk_atomic_constraint(B,X=X) :-
    nonvar(B), B = true, !.
mk_atomic_constraint(B,delay(BB,true)) :-
    nonvar(B), B = (_B1 & _B2), !,
    conj_append(B,true,BB).
mk_atomic_constraint(B,delay(BB,true)) :-
    nonvar(B), B = (_B1 or _B2), !,
    conj_append(B,true,BB).
mk_atomic_constraint(B,delay(B & true,true)) :-   % user-defned atomic predicates
    nonvar(B), \+ atomic_constr(B), !.
mk_atomic_constraint(B,B).                        % primitive atomic constraints


%%%%%%%%%%% equality involving CP

sat_eq_cp([T1 = T2|R1],R2,c,F) :-              % cp(...) = X --> substitute X
    var(T2),
    occur_check(T2,T1),
    !,
    (nonvar(T1), T1 = cp(A,_), nonvar(A), is_empty(A) ->
        T2 = {}
    ;
     nonvar(T1), T1 = cp(B,_), nonvar(B), is_empty(B) ->
        T2 = {}
    ;
        T2 = T1
    ),
    sat_step(R1,R2,_,F).
sat_eq_cp([T1 = T2|R1],R2,c,F) :-               % X = cp(...) --> cp(...) = X
    var(T1),!,
    sat_eq_cp([T2 = T1|R1],R2,_,F).
sat_eq_cp([T1 = T2|R1],R2,c,F) :-               % t = cp(...) --> cp(...) = t   (t not cp-term)
    nonvar(T1), T1 \= cp(_,_), !,
    sat_eq_cp([T2 = T1|R1],R2,_,F).

sat_eq_cp([T1 = T2|R1],R2,c,F) :-               % cp({},_) = T --> T={}
    nonvar(T1), T1 = cp(A,_), nonvar(A), is_empty(A),!,
    %write(rule(4)),nl,
    sunify(T2,{},C1),
    append(C1,R1,R3),
    sat_step(R3,R2,_,F).
sat_eq_cp([T1 = T2|R1],R2,c,F) :-               % cp(_,{}) = T --> T={}
    nonvar(T1), T1 = cp(B,_), nonvar(B), is_empty(B),!,
    %write(rule(5)),nl,
    sunify(T2,{},C1),
    append(C1,R1,R3),
    sat_step(R3,R2,_,F).
sat_eq_cp([T1 = E|R1],R2,c,F) :-                % cp(A,B) = {} --> A={} or B ={}
    nonvar(T1), T1 = cp(A,B),
    nonvar(E), is_empty(E),!,
    %write(rule(2)),nl,
    (   sat_step([A={}|R1],R2,_,F)
    ;
        sat_step([B={}|R1],R2,_,F)
    ).
sat_eq_cp([T1 = T2|R1],R2,c,F) :-               % e.g. cp({Z/S},{Y/R}) = {X/S} (special case)
    nonvar(T1), T1 = cp(A,B),
    tail(T2,TT2),
    same_tail(A,B,TT2),!,
    %write('special case cp({Z/S},{Y/R}) = {X/S}'),nl,
    TT2 = {},
    sat_step([T1 = T2|R1],R2,_,F).
sat_eq_cp([T1 = T2|R1],R2,c,F) :-               % cp(A,B) = cp(C,D)
    nonvar(T1), T1 = cp(A,B),
    nonvar(T2), T2 = cp(C,D),!,
    %write(rule(3)),nl,
    (   sunify(A,C,C1), append(C1,R1,R3),
        sunify(B,D,C2), append(C2,R3,R4),
        sat_step([A neq {},B neq {},C neq {},D neq {}|R4],R2,_,F)
    ;
        sat_step([T1 = {},T2 = {}|R1],R2,_,F)
    ).

sat_eq_cp([T1 = T2|R1],R2,c,F) :-               % cp(C,D)={...|cp(A,B)} (special case)
    nonvar(T1), T1 = cp(C,D),
    nonvar(T2), T2 = _ with _, tail(T2,TT2), nonvar(TT2), TT2 = cp(A,B),!,
    %write(rule(special)),nl,
    replace_tail(T2,{},Elems),
    (   sat_step([A = {}, Elems = cp(C,D)|R1],R2,_,F)
    ;
        sat_step([A neq {}, B = {}, Elems = cp(C,D)|R1],R2,_,F)
    ;
        sat_step([A neq {}, B neq {}, un(E1,E2,Elems), disj(E1,E2), subset(E1,cp(A,B)),
            disj(E2,cp(A,B)),
            un(N2,B,D),un(cp(N1,D),cp(A,N2),E2),
            un(N1,A,C),set(N1),set(N2),set(E1),set(E2)|R1],R2,_,F)
    ).

sat_eq_cp([T1 = T2|R1],R2,c,F) :-               % cp(A,B)={x|C}
    nonvar(T1), T1 = cp(A,B),
    nonvar(T2), T2 = _ with X,!,
    %write(rule(6)),nl,
    sunify(T2,N with X,C0), append(C0,R1,R1_0),
    sunify(A,A1 with N1,C1), append(C1,R1_0,R3),
    sunify(B,B1 with N2,C2), append(C2,R3,R4),
    sat_step([X nin N,N2 nin B1,N1 nin A1,X=[N1,N2],
        delay(un(cp({} with N1,B1),cp(A1,B1 with N2),N),false),
        set(N),set(A1),set(B1)|R4],R2,_,F).

%%%% auxiliary predicates for dealing with CP

cp_term(T) :-
    nonvar(T), T = cp(_,_).

cp_term(T,A,B) :-     % not used
    nonvar(T), T = cp(A,B).

is_cp(T,A,B) :-       % not used
    nonvar(T), T = cp(A,B),
    (set_term(A),! ; var(A)),
    (set_term(B),! ; var(B)).

%eq_cp_all(+S,+A,+B,C): S is a set term of the form cp(A,B) with tn with ... with t1,
%t1,...,tn either variables or pairs [x_i,y_i], and C is a list of constraint of the
%form x_i in A, y_i in B
%
eq_cp_all(cp(_,_) with [X,Y],A,B,[X in A,Y in B]) :-!.
eq_cp_all(S with [X,Y],A,B,[X in A,Y in B|RConst]) :-
    eq_cp_all(S,A,B,RConst).

not_cp(T) :-
    var(T),
    !.
not_cp(T) :-
    T \= cp(_,_).

one_cp(S1,S2,S3) :-
    (nonvar(S1), S1 = cp(_,_) ->
        true
    ;
     nonvar(S2), S2 = cp(_,_) ->
        true
    ;
        nonvar(S3),S3 = cp(_,_)
    ).

%cp_component(X,CP): true if X is one of the components of CP
cp_component(X,CP) :-
    CP = cp(A,B),
    (A==X ->
        true
    ;
        B==X
    ).
%
%cp_component(X,CP1,CP2): true if X is one of the components of either CP1 or CP2
cp_component(X,CP1,CP2) :-
    (cp_component(X,CP1) ->
        true
    ;
        cp_component(X,CP2)
    ).

%samevarcp(X,Y): true if X and Y are the same variable CP
samevarcp(X,Y) :-
    nonvar(X), X = cp(A,B), (var(A),! ; var(B)),
    nonvar(Y), Y = cp(C,D), (var(C),! ; var(D)),
    A == C, B == D.
%
%samevarcp(X,Y,Z): true if X and either Y or Z are the same variable CP
samevarcp(X,Y,Z) :-
    (samevarcp(X,Y) ->
        true
    ;
        samevarcp(X,Z)
    ).

tail_cp(X,T) :-
    nonvar(X), X = cp(A,B),!,
    (tail(A,T) ; tail(B,T)).
tail_cp(X,T) :-
    tail(X,T).

%%% this definition of gcp_to_set/2 can be improved
%%% because it doesn't convert a CP such as cp({A},{1})
%%% which could be easily converted into an extensional set.
%%% The case that can't be converted is cp({a/X},{1})
%
gcp_to_set(R,R) :-     %gcp_to_set(R,S): if R is not a ground CP, S is R; otherwise S is the
    var(R),!.          %extensional set corresponding to the cp R
gcp_to_set(R,S) :-
    R = cp(A,B),
    nonvar(A), A = cp(_,_),
    nonvar(B), B = cp(_,_),!,
    gcp_to_set(A,S1),
    gcp_to_set(B,S2),
    ((A == S1 -> true ; B == S2) ->
        S = R             %A or B couldn't be converted
    ;
        g_cp(S1,S2,S)
    ).
gcp_to_set(R,S) :-
    R = cp(A,B),
    nonvar(A), A = cp(_,_),!,
    gcp_to_set(A,S1),
    (A == S1 ->
        S = R             % A couldn't be converted
    ;
        g_cp(S1,B,S)
    ).
gcp_to_set(R,S) :-
    R = cp(A,B),
    nonvar(B), B = cp(_,_),!,
    gcp_to_set(B,S2),
    (B == S2 ->
         S = R            % B couldn't be converted
    ;
         g_cp(A,S2,S)
    ).
gcp_to_set(R,S) :-
    R = cp(A,B),
    ground(A),ground(B),!,
    g_cp(A,B,S).
gcp_to_set(R,R).

g_cp({},_,{}).
g_cp(A with X,B,CP) :-
    g_cp_elem(X,B,CPX),
    g_cp(A,B,CPA),
    g_union(CPX,CPA,CP).
g_cp_elem(_,{},{}).
g_cp_elem(X,B with Y,CP with [X,Y]) :-
    g_cp_elem(X,B,CP).


%%%%%%%%%%%  Set/Multiset Unification Algorithm  %%%%%%%%%%%%

sunify(X,Y,[]) :-                         % X = X
    X == Y, !.
sunify(T1,T2,[]) :-                       % t1 = t2, t1 and t2 either atoms or numbers
    (atom(T1) -> true ; number(T1)),
    (atom(T2) -> true ; number(T2)),!,
    T1 = T2.
sunify(T1,T2,[T1 = T2]) :-                % ris = t or cp(...) = t
    nonvar(T1),
    (ris_term(T1) -> true ; cp_term(T1)),!.
sunify(T1,T2,[T1 = T2]) :-                % t = ris or t = cp(...)
    nonvar(T2),
    (ris_term(T2) -> true ; cp_term(T2)),!. 
sunify(X,Y,[]) :-                         % X = Y, X and Y integer variables (patch for clpq)  
    var(X),var(Y),
    is_int_var(X),
    is_int_var(Y),!,
    solve_int(X is Y,_),
    X = Y.
sunify(X,Y,C) :-                          % X = t
    var(X),!,
    %write(rule(sunifyXt1)),nl,
    sunifyXt(X,Y,C).
sunify(X,Y,C) :-                          % t = Y ---> Y = t
    var(Y),!,
    %write(rule(sunifyXt2)),nl,
    %sunify(Y,X,C).
    sunifyXt(Y,X,C).   
sunify(int(X1,X2),T2,C) :-                % intervals
    %int_term(int(X1,X2)),  
    int_term(T2),!,  
    int_unify(int(X1,X2),T2,C).
sunify(int(X1,X2),T2,C) :-                % intervals
    %int_term(int(X1,X2)),
    set_term(T2),!,
    int_unify(int(X1,X2),T2,C).
sunify(T1,T2,C) :-                        % intervals
    int_term(T2), set_term(T1),!,
    int_unify(T2,T1,C).
sunify(X1 with X2,S,C) :-                 %
    tail2(X1 with X2,TR), tail2(S,TS),
    !,
    (tail(TR,TTR), tail(TS,TTS),          % {.../s(X)} = {../t(X)}
     samevar(TTR,TTS) ->
        %write('rule({t1/s(X)}={t2/t(X)})'),nl,
        stunify_ss_special(X1 with X2,S,TR,TS,C)
    ;
        %write('rule({t1/X}={t2/Y}'),nl,  % {.../R} = {../S},
        (b_getval(smode,prover(Strategies)),    % solving mode is prover([subset_unify,...]) 
         member(subset_unify,Strategies) ->              
           C = [subset(X1 with X2,S),subset(S,X1 with X2)]
        ;
           stunify_ss(X1 with X2,S,C)           
        )
    ).
%sunify(X1 mwith X2,Y,C) :-                % bag unification +{...} = +{...}
%    bag_tail(X1 mwith X2,BX),
%    bag_tail(Y,BY),
%    !,
%    (samevar(BX,BY) ->
%        stunify_bag_same(X1 mwith X2,Y,C)
%    ;
%        stunify_bag(X1 mwith X2,Y,C)
%    ).
sunify(X,Y,C) :-                          % f(...) = f(...)
    X=..[F|Ax], Y=..[F|Ay],
    !,
    sunifylist(Ax,Ay,C).

stunify_ss_special(R,S,TR,TS,C) :-        % non-admissible constraints
    (ris_term(TR,ris(CtrlExpr1 in _Dom1,_,_,P1,_)),CtrlExpr1 \== P1,
    var(TS),!
    ;
    ris_term(TS,ris(CtrlExpr1 in _Dom1,_,_,P1,_)),CtrlExpr1 \== P1,
    var(TR),!
    ;
    ris_term(TR,ris(CtrlExpr1 in _Dom1,_,_,P1,_)),CtrlExpr1 \== P1,
    ris_term(TS,ris(CtrlExpr2 in _Dom2,_,_,P2,_)),CtrlExpr2 == P2,!
    ;
    ris_term(TR,ris(CtrlExpr1 in _Dom1,_,_,P1,_)),CtrlExpr1 == P1,
    ris_term(TS,ris(CtrlExpr2 in _Dom2,_,_,P2,_)),CtrlExpr2 \== P2,!
    ),
    !,
    (final ->
        throw(setlog_excpt('non-admissible constraint'))
    ;
        C=[delay(R = S,false)]
    ).

stunify_ss_special(R,S,TR,TS,C) :-        % admissible constraints
    (samevar(TR,TS),!,                    % R and S are the same variable
     %write(rule({t1/'X'}={t2/'X'})),nl,
     stunify_samevar(R,S,TR,C)
     ;
     samevarris_simple(TR,TS),!,          % R and S are both "simple RIS" or S is a var.
     %write('rule({t1/ris(X)}={t2/ris(X)}-simple RIS or {t2/ris(X)} = {t1/X}'),nl,
     stunify_samevar_ris1(R,S,TR,TS,C)
     ;
     samevarris_simple_inv(TR,TS),!,      % R is a var. and S is a "simple RIS"
     %write('rule({t1/ris(X)}={t2/X}'),nl,
     stunify_samevar_ris1(S,R,TS,TR,C)
     ;
     samevarris_nonsimple(TR,TS),!,       % R and S are both "non-simple RIS"
     %write('rule({t1/ris(X)}={t2/ris(X)} - nonsimple RIS'),nl,
     stunify_samevar_ris2(R,S,TR,TS,C)
     ;
     stunify_ss(R,S,C)                    % S is a RIS with a non-var domain
    ).

samevarris_simple(R,S) :-      % R and S are simple RIS
    ris_term(R,ris(CtrlExpr1 in _Dom1,_,_,P1,_)),%var_ris(Dom1),
                               % counterexample: {a/ris(X in {c,b/D},a=a)} = {b/ris(Y in D,a=a)}.
    ris_term(S,ris(CtrlExpr2 in Dom2,_,_,P2,_)),var_ris(Dom2),
    CtrlExpr1 == P1,
    CtrlExpr2 == P2,!.
samevarris_simple(R,S) :-      % S is a var. and R is any RIS
    ris_term(R,ris(CtrlExpr1 in _Dom1,_,_,P1,_)),
    var(S),
    CtrlExpr1 == P1,!.
samevarris_simple_inv(R,S) :-  % R is a var. and S is any RIS
    ris_term(S,ris(CtrlExpr2 in _Dom2,_,_,P2,_)),
    var(R),
    CtrlExpr2 == P2,!.
samevarris_nonsimple(R,S) :-   % R and S are RIS and at least one is a "non-simple RIS"
    ris_term(R,ris(CtrlExpr1 in _Dom1,_,_,P1,_)),
    ris_term(S,ris(CtrlExpr2 in Dom2,_,_,P2,_)), var_ris(Dom2),
    CtrlExpr1 \== P1,
    CtrlExpr2 \== P2.

%%%%%%%%%%% var-set unification

sunifyXt(X,Y,[]) :-                           % X = t
    catch(unify_with_occurs_check(X,Y),_,fail),!.   
sunifyXt(X,Y,C) :-                            % X = {...|X} or X = {...|ris(Z in X,...,Z)}
    nonvar(Y),tail2(Y,T),
    tail(T,TT), samevar(X,TT), !,
    sunifyXt_special(T,X,Y,C).
    %write(rule('X'={t1/'X'})),nl.
  
sunifyXt_special(T,X,Y,[set(N)]) :-           % X = {...|X}
    var(T),!,
    replace_tail(Y,N,NewY),
    occur_check(X,NewY),
    X = NewY.
sunifyXt_special(T,X,Y,[set(N)]) :-           % X = {...|ris(Z in X,...,Z)}  (simple RIS)
    ris_term(T,ris(CtrlExpr in _Dom,_,_,P,_)),
    CtrlExpr == P,!,
    replace_tail(Y,N,NewY),
    occur_check(X,NewY),
    X = NewY.
sunifyXt_special(T,X,Y,C) :-                  % X = {...|ris(Z in X,...,f(Z))}  (non-admissible constraint)
    ris_term(T,ris(CtrlExpr in _Dom,_,_,P,_)),
    CtrlExpr \== P,!,
    (final ->
        throw(setlog_excpt('non-admissible constraint'))
    ;
        C = [delay(X = Y,false)]
    ).

%%%%%%%%%%% set-set unification

%%  distinct tail vars.
stunify_ss(R with X,S with Y,C) :-  % {t,...} = {t,...}
    X==Y,!,
    stunify1_2_3(R,S,X,Y,C).
stunify_ss(R with X,S with Y,C) :-  % ground case: {...} = {...}
    ground(X), ground(Y),!,
    (   sunify(X,Y,C1) ->
        stunify1_2_3(R,S,X,Y,C2),
        append(C1,C2,C)
    ;
        sunify(R,N with Y,C1),
        sunify(S,N with X,C2),
        append(C1,C2,C3),
        C = [set(N)|C3]
    ).
stunify_ss(R with X,S with Y,C) :-  % {...|X} = {...|Y}
    sunify(X,Y,C1),
    stunify1_2_3(R,S,X,Y,C2),
    append(C1,C2,C).
stunify_ss(R with X,S with Y,C) :-  % {...|X} = {...|Y} (permutativity)
    sunify(R,N with Y,C1),
    sunify(S,N with X,C2),
    append(C1,C2,C3),
    C = [set(N)|C3].

stunify1_2_3(R,S,_,_,C) :-          % 1
    sunify(R,S,C).
stunify1_2_3(R,S,_,Y,C) :-          % 2
    sunify(R,S with Y,C).
stunify1_2_3(R,S,X,_,C) :-          % 3
    sunify(R with X,S,C).

%%  same tail vars.
stunify_samevar(R with X,S with Y,_,C) :-   % {...|X} = {...|X}
    select_var(Z,S with Y,Rest),
    sunify(X,Z,C1),
    (   sunify(R,Rest,C2)            % 1
        %,write(rule({t1/'X'}={t2/'X'} - 'case 1')),nl
    ;
        sunify(R with X,Rest,C2)     % 2
        %,write(rule({t1/'X'}={t2/'X'} - 'case 2')),nl
    ;
        sunify(R,S with Y,C2)        % 3
        %,write(rule({t1/'X'}={t2/'X'} - 'case 3')),nl
    ),
    append(C1,C2,C).
stunify_samevar(R with X,S with Y,_,C) :-    % 4
    %write(rule({t1/'X'}={t2/'X'} - 'case 4')),nl,
    replace_tail(R,N,NewR),             %replace_tail2
    replace_tail(S with Y,N,NewSS),     %replace_tail2
    tail2(S with Y,TS),
    sunify(TS,N with X,C1),
    sunify(NewR,NewSS,C2),
    append(C1,C2,C3),
    C = [set(N)|C3].

stunify_samevar_ris1(R with X,S with Y,TR,TS,C) :-  % {...|ris(X)} = {...|ris(X)}, simple RIS
    %write(rule('{t1/ris(X)}={t2/ris(X)} - simple RIS')),nl,
    select_var(Z,S with Y,Rest),
    sunify(X,Z,C1),
    (%nl,write('case 1'),nl,
     replace_tail2(R,N1,NewR),
     replace_tail2(Rest,N2,NewS),
     final_sat([TR=N1 with X, X nin N1],C2),  %1
     final_sat([TS=N2 with X, X nin N2],C3),
     append([NewR=NewS|C1],C2,C12),
     append(C12,C3,C)
    ;
     %nl,write('case 2'),nl,
     sunify(R,Rest,C2),          %2
     append([X nin TR,X nin TS|C1],C2,C)
    ;
     %nl,write('case 3'),nl,
     replace_tail2(R,N,NewR),
     sunify(N with X,TR,C2),     %3
     %sunify(NewR,Rest,C3),
     %append([X nin N,X nin TS|C1],C2,C12), append(C12,C3,C)
     append([X nin N,X nin TS,delay(NewR=Rest,false)|C1],C2,C)
    ;
     %nl,write('case 4'),nl,
     replace_tail2(Rest,N,NewS),
     sunify(TS,N with X,C2),     %4
     %sunify(R,NewS,C3),
     %append([X nin TR,X nin N|C1],C2,C12), append(C12,C3,C)
     append([X nin TR,X nin N,delay(R=NewS,false)|C1],C2,C)
    ;
     %nl,write('case 5'),nl,
     sunify(R,S with Y,C2),      %5
     append(C1,C2,C)
    ;
     %nl,write('case 6'),nl,
     sunify(R with X,Rest,C2),   %6
     append(C1,C2,C)
    ).
stunify_samevar_ris1(R with X,S with Y,_TR,TS,C) :-
    %write('case 7'),nl,
    replace_tail(R,N,NewR),
    replace_tail(S with Y,N,NewSS),
    tail(TS,TTS),                %7
    %gamma(X)
    (var(TS),!,
     sunify(TTS,N with X,C1),
     sunify(NewR,NewSS,C2),
     append(C1,C2,C)
     ;
     ris_term(TS,ris(CE_Dom,V,Fl,P,PP)),
     CE_Dom = (CtrlExpr in _D),
     ctrl_expr(CtrlExpr,V,LV,CtrlExprNew),
     %
     chvar(LV,[],_Vars,[Fl,P,PP,CtrlExpr],[],_VarsNew,[FlNew,PNew,PPNew,CtrlExprNew]),
     %%%%%find_corr_list(CtrlExpr,CtrlExprNew,Vars,VarsNew),
     get_preconditions(PPNew,PosPre,_),
     %
     solve_expression(Z,PNew),
     mk_atomic_constraint(PPNew,PPNewD),
     conj_append(PosPre,FlNew,PreFlNew),
     mk_atomic_constraint(PreFlNew,FlNewD),
     %
     Z = X,
     %
     sunify(TTS,N with X,C1),
     sunify(NewR,NewSS,C2),
     append([FlNewD,PPNewD|C1],C2,C)
     %append(C1,C2,C).
    ).

stunify_samevar_ris2(R with X,S with Y,TR,TS,C) :-  % {...|ris(X)} = {...|ris(X)}, non-simple RIS
    %write(rule('{t1/ris(X)}={t2/ris(X)} - non-simple RIS')),nl,
    select_var(Yj,S with Y,Rest),
    (sunify(X,Yj,C1),
     %nl,write('case 1'),nl,
     replace_tail2(R,N1,NewR),
     replace_tail2(Rest,N2,NewS),
     sunify(TR,N1 with X,C2),    %1
     sunify(TS,N2 with X,C3),
     append([X nin N1,X nin N2,delay(NewR=NewS,false)|C1],C2,C12),
     append(C12,C3,C)
    ;
     sunify(X,Yj,C1),
     %nl,write('case 2'),nl,
     sunify(R,Rest,C2),          %2
     append([X nin TR,X nin TS|C1],C2,C)
    ;
     sunify(X,Yj,C1),
     %nl,write('case 3'),nl,
     replace_tail2(R,N,NewR),
     sunify(N with X,TR,C2),     %3
     append([X nin N,X nin TS,delay(NewR=Rest,false)|C1],C2,C)
    ;
     sunify(X,Yj,C1),
     %nl,write('case 4'),nl,
     replace_tail2(Rest,N,NewS),
     sunify(TS,N with X,C2),     %4
     append([X nin TR,X nin N,delay(R=NewS,false)|C1],C2,C)
    ;
     sunify(X,Yj,C1),
     %nl,write('case 5'),nl,
     sunify(R,S with Y,C2),      %5
     append(C1,C2,C)
    ;
     sunify(X,Yj,C1),
     %nl,write('case 6'),nl,
     sunify(R with X,Rest,C2),   %6
     append(C1,C2,C)
    ;
     %X \== Yj,
     %write('case 7'),nl,
     replace_tail(R,N,NewR),
     replace_tail(S with Y,N,NewSS),
     tail(TS,TTS),               %7
     %%% gamma(n)  & Z=v(n) & X=Z  (n is CtrlExprNew)
     ris_term(TS,ris(CE_Dom,V,Fl,P,PP)),
     CE_Dom = (CtrlExpr in _D),
     ctrl_expr(CtrlExpr,V,LV,CtrlExprNew),
     %
     chvar(LV,[],_Vars,[Fl,P,PP,CtrlExpr],[],_VarsNew,[FlNew,PNew,PPNew,CtrlExprNew]),
     %%%%%%find_corr_list(CtrlExpr,CtrlExprNew,Vars,VarsNew),
     get_preconditions(PPNew,PosPre,_),
     %
     solve_expression(Z,PNew),
     mk_atomic_constraint(PPNew,PPNewD),
     conj_append(PosPre,FlNew,PreFlNew),
     mk_atomic_constraint(PreFlNew,FlNewD),
     %
     Z = X,
     %
     %%% (Z2=u(n') & X=Z2 & phi(n') & Z2 nin Selems) or not phi(n') (n' is CtrlExpr2New and n = n')
     ris_term(TR,ris(CE_Dom2,V2,Fl2,P2,PP2)),
     CE_Dom2 = (CtrlExpr2 in _D2),
     ctrl_expr(CtrlExpr2,V2,LV2,CtrlExpr2New),
     %
     chvar(LV2,[],_Vars2,[Fl2,P2,PP2,CtrlExpr2],[],_Vars2New,[Fl2New,P2New,PP2New,CtrlExpr2New]),
     %%%%%%find_corr_list(CtrlExpr2,CtrlExpr2New,Vars2,Vars2New),
     get_preconditions(PP2New,PosPre2,NegPre2),
     CtrlExprNew=CtrlExpr2New,        % n' must be the same as n
     %
      (
       solve_expression(Z2,P2New),
       mk_atomic_constraint(PP2New,PP2NewD),
       conj_append(PosPre2,Fl2New,PreFl2New),
       mk_atomic_constraint(PreFl2New,Fl2NewD),
       %
       Z2 = X,
       %
       sunify(TTS,N with CtrlExprNew,C1),
       sunify(NewR,NewSS,C2),
       replace_tail2(S with Y,{},Selems),
       append([FlNewD,PPNewD,Fl2NewD,PP2NewD,Z2 nin Selems|C1],C2,C)
      ;
       %%% not phi(n)
       negate(Fl2New,NegFl),
       conj_append(PosPre2,PP2New,PrePP2New),
       conj_append(PrePP2New,NegFl,PreNegFl2),
       mk_atomic_constraint((PreNegFl2 or NegPre2),NegFlD2),
       %
       %sunify(TTS,N with X,C1),
       sunify(TTS,N with CtrlExpr2New,C1),
       sunify(NewR,NewSS,C2),
       append([FlNewD,PPNewD,NegFlD2|C1],C2,C)
      )
    ;
     %X \== Yj,
     final_sat([X neq Yj],_),
     %nl,write('case 8'),nl,
     replace_tail(R,N,NewR),
     replace_tail(S with Y,N,NewSS),
     tail(TS,TTS),               %8
     %%% gamma(n)  & Z=v(n) & X=Z  (n is CtrlExprNew)
     ris_term(TS,ris(CE_Dom,V,Fl,P,PP)),
     CE_Dom = (CtrlExpr in _D),
     ctrl_expr(CtrlExpr,V,LV,CtrlExprNew),
     %
     chvar(LV,[],_Vars,[Fl,P,PP,CtrlExpr],[],_VarsNew,[FlNew,PNew,PPNew,CtrlExprNew]),
     %%%%%find_corr_list(CtrlExpr,CtrlExprNew,Vars,VarsNew),
     get_preconditions(PPNew,PosPre,_),
     %
     solve_expression(Z,PNew),
     mk_atomic_constraint(PPNew,PPNewD),
     conj_append(PosPre,FlNew,PreFlNew),
     mk_atomic_constraint(PreFlNew,FlNewD),
     %
     Z = X,
     %
     %%% Z2=u(n') & X=Z2 & phi(n') & Z2 = Yj (n' is CtrlExpr2New and n = n')
     ris_term(TR,ris(CE_Dom2,V2,Fl2,P2,PP2)),
     CE_Dom2 = (CtrlExpr2 in _D2),
     ctrl_expr(CtrlExpr2,V2,LV2,CtrlExpr2New),
     %
     chvar(LV2,[],_Vars2,[Fl2,P2,PP2,CtrlExpr2],[],_Vars2New,[Fl2New,P2New,PP2New,CtrlExpr2New]),
     %%%%find_corr_list(CtrlExpr2,CtrlExpr2New,Vars2,Vars2New),
     get_preconditions(PP2New,PosPre2,_),
     CtrlExprNew=CtrlExpr2New,        % n' must be the same as n
     %
     solve_expression(Z2,P2New),
     mk_atomic_constraint(PP2New,PP2NewD),
     conj_append(PosPre2,Fl2New,PreFl2New),
     mk_atomic_constraint(PreFl2New,Fl2NewD),
     %
     Z2 = Yj,
     %
     sunify(TTS,N with CtrlExprNew,C1),
     sunify(NewR with Z2,NewSS,C2),
     append([FlNewD,PPNewD,Fl2NewD,PP2NewD|C1],C2,C)
    ).

sunifylist([],[],[]).
sunifylist([X|AX],[Y|AY],C) :-
    sunify(X,Y,C1),
    sunifylist(AX,AY,C2),
    append(C1,C2,C).

%%%%%%%%%%% Interval unification %%%%%%%%%%%%%%%%%

int_unify(int(L,H),T2,C) :-                          % int(t1,t2) = {}
    nonvar(T2), is_empty(T2), !,
    C = [integer(H), integer(L), H < L].

int_unify(int(L1,H1),int(L2,H2),[]) :-               % int(t1,t2) = int(a,b), a =< b
    ground(int(L2,H2)), L2 =< H2,!,
    L1 = L2, H1 = H2.
int_unify(int(L1,H1),int(L2,H2),[]) :-               % int(a,b) = int(t1,t2), a =< b, \+ground(int(t1,t2))
    ground(int(L1,H1)), L1 =< H1,!,
    L1 = L2, H1 = H2.

int_unify(T1,T2,C) :-                                % int(t1,t2) = int(s1,s2)
    T1 = int(L1,H1), T2 = int(L2,H2),
    \+ground(T1), \+ground(T2),
    !,
    %(   C = [T1 neq {}, T2 neq {}, L1 = L2, H1 = H2]
    (   C = [L1 =< H1, L2 =< H2, L1 = L2, H1 = H2]
    ;
    %   C = [T1 = {}, T2 = {}]
        C = [L1 > H1, L2 > H2]
    ).

int_unify(int(A,B),T2,[]) :-                         % int(a,b) = T2   (novar(a) and novar(b), a>b, T2 var or {})
    integer(A), integer(B), A > B,!,
    T2 = {}.
int_unify(int(A,B),T2,C) :-                          % int(a,b) = T2  (novar(a) and novar(b), a =< b, T2 var or {...})
    integer(A), integer(B), A =< B,!,
    final_sat([T2 = R with A, A nin R, set(R)],C1),
    A1 is A + 1,
    int_unify(int(A1,B),R,C2),
    append(C1,C2,C).
int_unify(T1,T2,C) :-                                % int(A,B) = {...}   (var(A) or var(B))
    T2 = _ with _, T1 = int(A,B),
    b_getval(rw_int,RWInt),
    (apply_st(RWInt,T1,S) ->
        C = [S = T2]
    ;
        (\+contains_var(T1,T2) ->             % T2 is not a variable; T2 may contain T1
            append(RWInt,[[T1,T2]],RWInt_),   % check with int(A,B) = {1/int(A,B)}
            b_setval(rw_int,RWInt_)           % if \+contains_var(T1,T2) isn't there it goes into a loop
        ;
            true
        ),
        C = [subset(T2,T1), size(T2,K), K is B-A+1]
    ).


%%%%%%%%%%% Multiset unification %%%%%%%%%%%%%%%%%

%stunify_bag_same(R mwith X, S mwith Y, C) :-   % +{...|X} = +{...|X}
%    de_tail(R mwith X,ZX),
%    de_tail(S mwith Y,ZY),
%    sunify(ZX,ZY,C).
%
%stunify_bag(R mwith X, S mwith Y, C) :-        % +{...|X} = +{...|Y}
%    sunify(X,Y,C1),
%    sunify(R,S,C2),
%    append(C1,C2,C).
%stunify_bag(R mwith X, S mwith Y,C) :-
%    sunify(R, N mwith Y, C1),
%    sunify(S, N mwith X, C2),
%    append(C1,C2,C3),
%    C = [bag(N)|C3].

%%%%%% auxiliary predicates for unification

select_var(_,S,_) :-
    var(S), !, fail.
select_var(Z, R with Z, R).
select_var(Z, R with Y, A with Y) :-
    select_var(Z, R, A).


%%%%%%%%%%%%%%%%%%%%%% inequality (neq/2)

%solved form: X neq T, var(X) & \+simple_integer_expr(T) & \+occurs(X,T)
%
sat_neq([X neq T|R1],[X neq T|R2],Stop,nf) :-         % X neq t (nf-irreducible form)
    var(X),
    \+ simple_integer_expr(T),
    !,
    sat_step(R1,R2,Stop,nf).

sat_neq([T1 neq T2|_R1],_R2,_R,_F) :-                 % t1 neq t1
    T1 == T2,
    !,
    fail.

%%%%%%%%%%%% switch cases
%%%-RIS
sat_neq([T1 neq T2|R1],R2,R,F) :-                     % ris neq t, t neq ris, ris neq ris
    (   nonvar(T1), ris_term(T1) ->
        true
    ;
        nonvar(T2), ris_term(T2)
    ),
    !,
    sat_neq_ris([T1 neq T2|R1],R2,R,F).
%%%-CP
sat_neq([T1 neq T2|R1],R2,R,F) :-                     % cp neq t, t neq cp, cp neq cp
    (   nonvar(T1), T1 = cp(_,_) ->
        true
    ;
        nonvar(T2), T2 = cp(_,_)
    ),
    !,
    sat_neq_cp([T1 neq T2|R1],R2,R,F).
%%%-variables
sat_neq([T1 neq T2|R1],R2,R,F) :-                     % X neq t, t neq X, X neq Y
    (   var(T1) ->
        true
    ;
        var(T2)
    ),
    !,
    sat_neq_var([T1 neq T2|R1],R2,R,F).
%%%-intervals
sat_neq([T1 neq T2|R1],R2,R,F) :-                     % int(t1,t2) neq t, t neq int(t1,t2), int(t1,t2) neq int(s1,s2)
    (   nonvar(T1), int_term(T1) ->
        true
    ;
        nonvar(T2), int_term(T2)
    ),
    !,
    sat_neq_intv([T1 neq T2|R1],R2,R,F).
%%%-pairs
sat_neq([T1 neq T2|R1],R2,R,F) :-                     % [a,b] neq [c,d]
    nonvar(T1), T1 = [_,_],
    nonvar(T2), T2 = [_,_],!,
    sat_neq_pair([T1 neq T2|R1],R2,R,F).
%%%-all other terms (including extensional sets/multisets)
sat_neq([T1 neq T2|R1],R2,R,F) :-                     % t1 neq t2
    nonvar(T1), nonvar(T2),!,
    sat_neq_nn([T1 neq T2|R1],R2,R,F).

%%%%%%%%%%%% variables
sat_neq_var([T1 neq T2|R1],R2,R,F) :-                 % X neq t (t not ris-term)
    var(T1), nonvar(T2), !,
    sat_neq_vn([T1 neq T2|R1],R2,R,F).
sat_neq_var([T1 neq T2|R1],R2,c,F) :-                 % t neq X
    nonvar(T1), var(T2),!,
    sat_neq([T2 neq T1|R1],R2,_,F).
sat_neq_var([T1 neq T2|R1],R2,R,F) :-                 % X neq Y
    var(T1), var(T2),!,
    sat_neq_vv([T1 neq T2|R1],R2,R,F).

% variable and general non-variable term
sat_neq_vn([X neq T|R1],R2,c,F) :-               % X neq t[X]
    is_ker(T),
    occurs(X,T),!,
    sat_step(R1,R2,_,F).
sat_neq_vn([X neq T|R1],R2,c,F) :-               % X neq {... | X}
    T = _S with _,
    tail2(T,TT), samevar_or_ris(X,TT),
    !,
    (   sat_in([Z in X,Z nin T|R1],R2,_,F)
    ;
        sat_nin([Z nin X,Z in T|R1],R2,_,F)
    ;
        sat_nset([nset(X)|R1],R2,_,F)
    ).
sat_neq_vn([X neq T|R1],R2,c,F) :-               % X neq {...,t[X],...}
    T = _S with _,
    occurs(X,T),!,
    sat_step(R1,R2,_,F).
sat_neq_vn([X neq T|R1],[solved(X neq T,var(X),1)|R2],c,F) :-
    simple_integer_expr(T),                % X neq t, t simple integer expr
    is_int_var(X), !,
    solve_int(X neq T,_),
    sat_integer([integer(X)|R1],R2,_,F).
sat_neq_vn([C|R1],[C|R2],Stop,F) :-              % X neq t (irreducible form)
    sat_step(R1,R2,Stop,F).

samevar_or_ris(_X,T) :-
    nonvar(T),
    !,
    ris_term(T).
samevar_or_ris(X,T) :-
    samevar(X,T).

% variable terms
sat_neq_vv([X neq Y|_],_,_,_F) :-                % X neq X
    samevar(X,Y),
    !,
    fail.
sat_neq_vv([T1 neq T2|R1],R2,c,F) :-             % Y neq X --> X neq Y
    T1 @> T2,
    !,
    sat_neq([T2 neq T1|R1],R2,_,F).
sat_neq_vv([X neq Y|R1],[solved(X neq Y,(var(X),var(Y)),1)|R2],c,F) :-  % X neq Y, X,Y domain variables
    is_int_var(X),
    is_int_var(Y),!,
    solve_int(X neq Y,_),
    sat_integer([integer(X),integer(Y)|R1],R2,_,F).
sat_neq_vv([C|R1],[C|R2],Stop,F) :-              % X neq Y (irreducible form)
    sat_step(R1,R2,Stop,F).

%%%%%%%%%%%% intervals
%sat_neq_intv([T1 neq T2|R1],[T1 neq T2|R2],Stop,nf) :- % unbounded intervals int(A,B) neq {}
%    nonvar(T1), T1 = int(A,B), var(A), var(B),         % delayed until final_sat is called 
%    nonvar(T2), is_empty(T2),!,
%    sat_step(R1,R2,Stop,nf).
sat_neq_intv([T1 neq T2|R1],R2,R,F) :-                 % unbounded intervals int(A,B) neq t
    int_term(T1), \+ground(T1), !,
    sat_neq_ui([T1 neq T2|R1],R2,R,F).
sat_neq_intv([T1 neq T2|R1],R2,R,F) :-                 % unbounded intervals t neq int(A,B)
    int_term(T2), \+ground(T2), !,
    sat_neq_ui([T2 neq T1|R1],R2,R,F).
sat_neq_intv([T1 neq T2|R1],R2,R,F) :-                 % bounded intervals int(a,b) neq t
    nonvar(T1), T1 = int(A,B),
    integer(A), integer(B),!,
    sat_neq_i([T1 neq T2|R1],R2,R,F).
sat_neq_intv([T1 neq T2|R1],R2,R,F) :-                 % bounded intervals t neq int(a,b)
    nonvar(T2), T2 = int(A,B),
    integer(A), integer(B),!,
    sat_neq_i([T2 neq T1|R1],R2,R,F).

% unbounded intervals
sat_neq_ui([int(A,B) neq T2|R1],R2,c,F) :-       % int(A,B) neq empty
    nonvar(T2), is_empty(T2),
    !,
    sat_step([A =< B|R1],R2,_,F).
sat_neq_ui([int(A,B) neq T2|R1],R2,c,F) :-       % int(A,B) neq {S|R}
    nonvar(T2), T2 = _ with _,
    !,
   (    sat_step([A =< Z, Z =< B, Z nin T2|R1],R2,_,F)
    ;
        sat_step([Z < A, Z in T2|R1],R2,_,F)
    ;
        sat_step([B < Z, Z in T2|R1],R2,_,F)
    ).
sat_neq_ui([int(A,B) neq T2|R1],R2,c,F) :-       % int(A,B) neq int(C,D)
    nonvar(T2), T2 = int(C,D),!,
    (
        sat_step([A =< B, C > D|R1],R2,_,F)
    ;  
        sat_step([A > B, C =< D|R1],R2,_,F)
    ;  
        sat_step([A =< B, C =< D, A neq C|R1],R2,_,F)
    ;
        sat_step([A =< B, C =< D, B neq D|R1],R2,_,F)
    ).
sat_neq_ui([_T1 neq _T2|R1],R2,c,F) :-           % int(A,B) neq t  (t non-set term)
    sat_step(R1,R2,_,F).

% bounded intervals (a,b,c,d constants) 
sat_neq_i([T1 neq T2|_R1],_R2,_,_F) :-           % int(a,b) neq int(c,d), a>b, c>d   
    nonvar(T1), nonvar(T2),
    is_empty(T1),is_empty(T2),!, fail.
sat_neq_i([T1 neq T2|R1],R2,c,F) :-              % int(a,b) neq int(c,d)
    closed_intv(T1,A1,_B1), closed_intv(T2,A2,_B2),
    A1 \== A2,!,
    sat_step(R1,R2,_,F).
sat_neq_i([T1 neq T2|R1],R2,c,F) :-              % int(a,b) neq int(c,d)
    closed_intv(T1,_A1,B1), closed_intv(T2,_A2,B2),
    B1 \== B2,!,
    sat_step(R1,R2,_,F).
sat_neq_i([T1 neq T2|R1],R2,c,F) :-              % int(a,b) neq {S|R}, (special)
    set_length(T2,SetL),
    int_length(T1,IntL),
    SetL < IntL, !,
    sat_step(R1,R2,_,F).
sat_neq_i([T1 neq T2|R1],R2,c,F) :-              % int(a,b) neq {S|R}
    nonvar(T2), T2 = _ with _, !,
    (sat_in([Z in T1, Z nin T2, integer(Z) | R1],R2,_,F)      % (i)
    ;
     sat_nin([Z nin T1, Z in T2| R1],R2,_,F)                  % (ii)
    ).
sat_neq_i([_T1 neq _T2|R1],R2,c,F) :-            % int(a,b) neq t (t non-set term)
    sat_step(R1,R2,_,F).

%%%%%%%%%%%% general non-variable terms
sat_neq_nn([F neq G|R1],R2,c,Fin) :-             % ground case: t1 neq t2
    ground(F),ground(G),!,
    g_neq(F,G),
    sat_step(R1,R2,_,Fin).
sat_neq_nn([F neq G|R1],R2,c,Fin) :-             % t1 neq t2
    functor(F,Fname,Far),functor(G,Gname,Gar),
    (Fname \== Gname ; Far \== Gar),!,
    sat_step(R1,R2,_,Fin).
sat_neq_nn([F neq G|R1],R2,c,Fin) :-             % t1 neq t2
    functor(F,Fname,Far),functor(G,Gname,Gar),
    Fname == Gname, Far == Gar,
    Fname \== with, 
    %Fname \== mwith,
    F =.. [_|Flist], G =.. [_|Glist],!,
    memberall(A,B,Flist,Glist),
    sat_neq([A neq B|R1],R2,_,Fin).

% sets
sat_neq_nn([T1 neq T2|R1],R2,c,F) :-             % inequality between sets
    T1 = _S with _A, T2 = _R with _B,     
    \+sunify(T1,T2,_),!,
    sat_step(R1,R2,_,F).
sat_neq_nn([T1 neq T2|R1],R2,c,F) :-             % inequality between sets
    T1 = _S with _A, T2 = _R with _B,            % {A|S} neq {B|R} (i)
    sat_in([Z in T1, Z nin T2 | R1],R2,_,F).
sat_neq_nn([T1 neq T2|R1],R2,c,F) :-             % inequality between sets
    T1 = _S with _A, T2 = _R with _B,!,          % {A|S} neq {B|R} (ii)
    sat_in([Z in T2, Z nin T1 | R1],R2,_,F).
%sat_neq_nn([_T1 neq _T2|_R1],_R2,c,_F) :-       % other aggregates?
%    other_aggrs(off),!,fail.

% multisets
%sat_neq_nn([T1 neq T2|R1],R2,c,F) :-            % inequality between multisets
%    nonvar(T1),nonvar(T2),                      % with the same tail variables
%    bag_tail(T1,TT1), bag_tail(T2,TT2),
%    samevar(TT1,TT2),!,
%    de_tail(T1,DT1), de_tail(T2,DT2),
%    sat_neq([DT1 neq DT2|R1],R2,_,F).
%sat_neq_nn([T1 neq T2|R1],R2,c,F) :-             % inequality between multisets
%    T1 = _S mwith A, T2 = R mwith B,             % with distinct tail variables
%    sat_neq([A neq B, A nin R| R1],R2,_,F).
%sat_neq_nn([T1 neq T2|R1],R2,c,F) :-
%    T1 = _S mwith A, T2 = R mwith B,!,
%    sunify(R mwith B, _N mwith A,C),
%    append(C,R1,R3),
%    sat_in([Z in T2, Z nin T1 | R3],R2,_,F).

%%%%%%%%%%%% RIS
sat_neq_ris([T1 neq T2|R1],R2,c,F) :-             % ris(...) neq t or t neq ris(...) (t any term, including var and RIS)
    (   sat_in([Z in T1,Z nin T2,set(T1),set(T2)|R1],R2,_,F)
    ;
        sat_nin([Z nin T1,Z in T2,set(T1),set(T2)|R1],R2,_,F)
    ;
        sat_nset([nset(T1)|R1],R2,_,F)
    ).

%%%%%%%%%%%% CP
sat_neq_cp([T1 neq T2|R1],R2,c,F) :-               % cp(A,A) neq cp(C,C)
    nonvar(T1), T1 = cp(A,B), A == B,
    nonvar(T2), T2 = cp(C,D), C == D,!,
    %write(rule(cp neq cp)),nl,
    sat_step([A neq C|R1],R2,_,F).
sat_neq_cp([T1 neq T2|R1],R2,c,F) :-               % cp(...) neq t or t neq cp(...) (t any term, including var and CP)
    %write(rule(cp neq t)),nl,
    (   sat_in([N in T1,N nin T2,set(T1),set(T2)|R1],R2,_,F)
    ;
        sat_nin([N nin T1,N in T2,set(T1),set(T2)|R1],R2,_,F)
    ).

%%%%%%%%%%%% pairs
sat_neq_pair([[T1,T2] neq [S1,S2]|R1],R2,c,F) :-   % [t1,t2] neq [s1,s2]
    (   T1 == T2, S1 == S2,!,
        sat_neq([T1 neq S1|R1],R2,_,F)
        ;
        T1 == S2, T2 == S1,!,
        sat_neq([T1 neq T2|R1],R2,_,F)
        ;
        ground(T1), ground(S1),
        T1 \== S1, !,
        sat_step(R1,R2,_,F)
        ;
        ground(T2), ground(S2),
        T2 \== S2, !,
        sat_step(R1,R2,_,F)
        ;
        sat_neq([T1 neq S1|R1],R2,_,F)
        ;
        sat_neq([T2 neq S2|R1],R2,_,F)
    ).

%%%%%%%%%%%%
%%%%%%%%%%%% Rewriting rules for arithmetic constraints %%%%%%%%%%%%
%%%%%%%%%%%%

sat_eeq([X is E|R1],R2,c,F) :-        % integer equality (is/2)
    ground(E),!,
    simple_arithm_expr(X),            % to catch type errors within {log}
    arithm_expr(E),
    X is E,
    sat_step(R1,R2,_,F).
sat_eeq([X is E|R1],R2,c,F) :-        % integer equality
    simple_integer_expr(X),           % to catch type errors within {log}
    integer_expr(E),
    allintvars(X is E,IntC2),
    solve_int(X is E,IntC1),
    append(IntC1,IntC2,IntC),
    append(IntC,R1,Newc),
    sat_step(Newc,R2,_,F).

sat_crel([Rel|R1],R2,c,F) :-          % integer comparison relations (=<,<,>=,>)
    Rel =.. [_OP,E1,E2],
    ground(E1), ground(E2),!,
    arithm_expr(E1),                  % to catch type errors within {log}
    arithm_expr(E2),
    call(Rel),
    sat_step(R1,R2,_,F).
sat_crel([Rel|R1],R2,c,F) :-
    Rel =.. [_OP,E1,E2],
    integer_expr(E1),                 % to catch type errors within {log}
    integer_expr(E2),
    solve_int(Rel,IntC1),
    allintvars(Rel,IntC2),
    append(IntC1,IntC2,IntC),
    append(IntC,R1,R3),
    sat_step(R3,R2,_,F).

allintvars(E,Evars) :-     % true if E is an integer expression and Evars
    E =.. [_F|Args],       % is a list containing a contraint integer(X) for
    addint(Args,Evars).    % each integer variable X in E

addint([], []).
addint([X|R], [integer(X)|Rvars]) :-
    var(X),
    !,
    addint(R,Rvars).
addint([X|R], Rvars) :-
    number(X),
    !,
    integer(X),
    addint(R,Rvars).
addint([E|R], Allvars) :-
    allintvars(E,Evars),
    addint(R,Rvars),
    append(Evars,Rvars,Allvars).


%%%%%%%%%%%%
%%%%%%%%%%%% Rewriting rules for set/bag/list/interval constraints %%%%%%%%%%%%
%%%%%%%%%%%%

%%%%%%%%%%%%%%%%%%%%%% membership (in/2)

sat_in([T in I|R1],R2,R,F) :-                 % variable
    var(I),
    !,
    sat_in_v([T in I|R1],R2,R,F).
sat_in([T in I|R1],R2,R,F) :-                 % bounded interval: t in int(a,b)
    closed_intv(I,L,H),!,
    sat_in_i([T in int(L,H)|R1],R2,R,F).
sat_in([T in I|R1],R2,R,F) :-                 % unbounded interval: t in int(A,B)
    int_term(I),!,
    sat_in_ui([T in I|R1],R2,R,F).
sat_in([T in I|R1],R2,R,F) :-                 % ris
    ris_term(I),!,
    sat_in_ris([T in I|R1],R2,R,F).
sat_in([T in I|R1],R2,R,F) :-                 % cp
    nonvar(I), I = cp(_,_),!,
    sat_in_cp([T in I|R1],R2,R,F).
sat_in([T in I|R1],R2,R,F) :-                 % extensional set/multiset/list;  t in {...}
    nonvar(I),!,
    sat_in_s([T in I|R1],R2,R,F).

sat_in_v([T in X|R1],R2,c,F) :-               % t in X, set only
%    other_aggrs(off),!,
    sunify(X,N with T,C1),
    append(C1,R1,R3),
    (compute_sols ->
         sat_step([T nin N,set(N)|R3],R2,_,F)
     ;
         sat_step([set(N)|R3],R2,_,F)
    ).

%sat_in_v([T in X|R1],R2,c,F) :-               % t in X, set
%    sunify(X,N with T,C1),
%    append(C1,R1,R3),
%    (b_getval(smode,solver) ->
%         sat_step([T nin N,set(N)|R3],R2,_,F)
%     ;
%         sat_step([set(N)|R3],R2,_,F)
%    ).
%sat_in_v([T in X|R1],R2,c,F) :-               % t in X, multiset
%    sunify(X,N mwith T,_),
%    sat_bag([bag(N)|R1],R2,_,F).
%sat_in_v([T in X|R1], [solved(T in X,(var(X),occur_check(X,T)),3),list(X)|R2],Stop,F) :-
%    occur_check(X,T),                   % t in X, list (irreducible form)
%    sat_step(R1,R2,Stop,F).

sat_in_i([T in int(A,B)|R1],R2,c,F) :-        % bounded interval: t in int(a,b)
    simple_integer_expr(T),!,
    solve_int(T in int(A,B),IntC),
    append(IntC,R1,R3),
    sat_integer([integer(T)|R3],R2,_,F).

sat_in_ui([T in I|R1],R2,c,F) :-              % unbounded interval: t in int(A,B)
    simple_integer_expr(T),!,                 % either A or B vars
    I=int(A,B),
    solve_int(T >= A,IntC1),
    solve_int(T =< B,IntC2),
    append(IntC1,IntC2,IntC),
    append(IntC,R1,R3),
    sat_integer([integer(T)|R3],R2,_,F).

sat_in_s([T in Aggr|R1],R2,c,F) :-            % t in {...,t,...}
    set_member_strong(T,Aggr),!,
    sat_step(R1,R2,_,F).
sat_in_s([T in Aggr|R1],R2,c,F) :-            % set/multiset/list (case i): t in {...}
    aggr_comps(Aggr,A,_R),
    sunify(A,T,C),
    append(C,R1,R3),
    sat_step(R3,R2,_,F).
sat_in_s([T in Aggr|R1],R2,c,F) :-            % set/multiset/list (case ii): t in {...}
    aggr_comps(Aggr,_A,R),!,
    sat_in([T in R|R1],R2,_,F).

sat_in_ris([X in T1|R1],[X in T1|R2],Stop,nf) :-   % X in ris(v,int(A,B),...) ,  var(A) or var(B)
    ris_term(T1,ris(CE_Dom,_,_,_,_)),
    CE_Dom = (_ in Dom),
    open_intv(Dom),!,
    sat_step(R1,R2,Stop,nf).
sat_in_ris([X in T1|R1],R2,c,F) :-            %  X in ris(v,D,...)
    ris_term(T1,ris(CE_Dom,V,Fl,P,PP)),
    CE_Dom = (CtrlExpr in D),
    (var(D),! ; nonopen_intv(D)),
    ctrl_expr(CtrlExpr,V,LV,CtrlExprNew),
    chvar(LV,[],_Vars,[Fl,P,PP,CtrlExpr],[],_VarsNew,[FlNew,PNew,PPNew,CtrlExprNew]),
    %%%%find_corr_list(CtrlExpr,CtrlExprNew,Vars,VarsNew),
    solve_expression(Z,PNew),
    X = Z,
    get_preconditions(PPNew,PosPre,_),
    mk_atomic_constraint(PPNew,PPNewD),
    conj_append(PosPre,FlNew,PreFlNew),
    mk_atomic_constraint(PreFlNew,FlNewD),
    sat_in([CtrlExprNew in D,set(D),FlNewD,PPNewD |R1],R2,_,F).

sat_in_cp([T in cp(A,B)|R1],R2,c,F) :-       % [X,Y] in cp(A,B)
    sat_eq([T = [X,Y], X in A,Y in B|R1],R2,_,F).


%%%%%%%%%%%%%%%%%%%%%% non-membership (nin/2)

%solved form: T nin A, var(A) & \+occurs(A,T)
%             or nonvar(A) & ris_term(I,ris(_ in Dom,_,_,_,_)) & var_ris(Dom)
%
sat_nin([T nin A|R1],[T nin A|R2],Stop,nf) :- % t nin X, nf-irreducible form
    var(A),
    !,
    sat_step(R1,R2,Stop,nf).

sat_nin([T nin A|_R1],_R2,c,_F) :-           % t nin {...,t,...} --> false
    set_member_strong(T,A),!,
    fail.
sat_nin([T nin A|R1],R2,c,F) :-              % ground set/multiset/list/interval:
    ground(T), ground(A), A \= cp(_,_), !, % t nin {A|R} or t nin +{A|R} or t nin [A|R] or t nin int(a,b)
    \+ g_member(T,A),
    sat_step(R1,R2,_,F).
sat_nin([T nin A|R1],R2,c,F) :-              % t nin X, t[X]
    var(A), occurs(A,T),!,
    sat_step(R1,R2,_,F).
sat_nin([T nin A|R1],[T nin A|R2],Stop,F) :- % t nin X, irreducible form
    var(A),!,
    sat_step(R1,R2,Stop,F).
sat_nin([_T nin A|R1],R2,c,F) :-             % t nin {}  or  t nin []  or  t nin int(a,b) with a>b
    nonvar(A), empty_aggr(A),!,
    sat_step(R1,R2,_,F).
sat_nin([T nin I|R1],R2,R,F) :-              % t nin int(A,B)
    int_term(I),!,
    sat_nin_int([T nin I|R1],R2,R,F).
sat_nin([T nin I|R1],R2,R,F) :-              % t nin ris(v,D,...)
    ris_term(I),!,
    sat_nin_ris([T nin I|R1],R2,R,F).
sat_nin([T nin I|R1],R2,R,F) :-              % t nin cp(...)
    nonvar(I), I = cp(_,_),!,
    sat_nin_cp([T nin I|R1],R2,R,F).
sat_nin([T1 nin A|R1],R2,c,F) :-             % t nin {...} or t nin +{...} or t nin [...]
    nonvar(A), aggr_comps(A,T2,S),!,
    sat_neq([T1 neq T2,T1 nin S|R1],R2,_,F).
sat_nin([_T nin A|R1],R2,c,F) :-             % t nin a, a not a set neither an interval
    nonvar(A),
    sat_step(R1,R2,_,F).

sat_nin_int([R nin I|R1],R2,c,F) :-         % bounded/unbounded interval: t nin int(A,B)
%   int_term(I),                            %   (case i)
    simple_integer_expr(R),
    I=int(S,_T),
    solve_int(R + 1 =< S,IntC),
    append(IntC,R1,R3),
    sat_integer([integer(R),integer(S)|R3], R2, _, F).
sat_nin_int([R nin I|R1],R2,c,F) :-         %   (case ii)
%   int_term(I),
    simple_integer_expr(R),
    I=int(_S,T),
    solve_int(T + 1 =< R,IntC),
    append(IntC,R1,R3),
    sat_integer([integer(R),integer(T)|R3], R2, _, F).
sat_nin_int([R nin _I|R1], R2, c, F) :-     %   (case iii)
%   int_term(I),!,
    sat_ninteger([ninteger(R)|R1], R2, _, F).

sat_nin_ris([X nin I|R1],[X nin I|R2],Stop,F) :- % ris: X nin ris{v,D,...) (var-ris D): irreducible
    ris_term(I,ris(_ in Dom,_,_,_,_)),
    var_ris(Dom),!,
    sat_step(R1,R2,Stop,F).
sat_nin_ris([_X nin I|R1],R2,c,F) :-        % ris: X nin ris{v,{},...) -> true
    ris_term(I,ris(_ in Dom,_,_,_,_)),
    is_empty(Dom),!,
    sat_step(R1,R2,_,F).

sat_nin_ris([X nin T1|R1],[X nin T1|R2],Stop,nf) :-
    ris_term(T1,ris(CE_Dom,_,_,_,_)),
    CE_Dom = (_ in Dom), nonvar_ris(Dom),
    open_intv(Dom),!,
    sat_step(R1,R2,Stop,nf).
sat_nin_ris([X nin I|R1],R2,c,F) :-          % ris: X nin ris{v,{...},...)
    ris_term(I,ris(CE_Dom,V,Fl,P,PP)),
    nonvar(CE_Dom), CE_Dom = (CtrlExpr in Dom),
    nonopen_intv(Dom),
    CtrlExpr == P,
    !,
    (   sat_step([X nin Dom |R1],R2,_,F)
    ;
        ctrl_expr(CtrlExpr,V,LV,CtrlExprNew),
        CtrlExprNew=X,
        chvar(LV,[],_Vars,[Fl,P,PP,CtrlExpr],[],_VarsNew,[FlNew,_PNew,PPNew,CtrlExprNew]),
        %%%%%find_corr_list(CtrlExpr,CtrlExprNew,Vars,VarsNew),
        get_preconditions(PPNew,PosPre,NegPre),
        negate(FlNew,NegFl),
        conj_append(PosPre,PPNew,PrePPNew),
        conj_append(PrePPNew,NegFl,PreNegFl),
        mk_atomic_constraint((PreNegFl or NegPre),NegFlD),
        sat_step([NegFlD |R1],R2,_,F)
    ).
sat_nin_ris([X nin I|R1],R2,c,F) :-          % ris: X nin ris{v,{...},...)
    ris_term(I,ris(CE_Dom,V,Fl,P,PP)),
    nonvar(CE_Dom), CE_Dom = (CtrlExpr in Dom), nonvar_ris(Dom),!,
    nonopen_intv(Dom),
    ctrl_expr(CtrlExpr,V,LV,CtrlExprNew),
    get_rest(Dom,CtrlExprNew,D,CNS),
    (nonvar(CNS) ->
        append(CNS,R1,R3),
        chvar(LV,[],_Vars,[Fl,P,PP,CtrlExpr],[],_VarsNew,[FlNew,PNew,PPNew,CtrlExprNew]),
        %%%%%find_corr_list(CtrlExpr,CtrlExprNew,Vars,VarsNew),
        solve_expression(Z,PNew),
        get_preconditions(PPNew,PosPre,NegPre),
        mk_atomic_constraint(PPNew,PPNewD),
        (   conj_append(PosPre,FlNew,PreFlNew),
            mk_atomic_constraint(PreFlNew,FlNewD),
            sat_step([FlNewD,PPNewD,X neq Z,X nin ris(CtrlExpr in D,V,Fl,P,PP) |R3],R2,_,F)
        ;
            negate(FlNew,NegFl),
            conj_append(PosPre,PPNew,PrePPNew),
            conj_append(PrePPNew,NegFl,PreNegFl),
            mk_atomic_constraint((PreNegFl or NegPre),NegFlD),
            sat_step([NegFlD,X nin ris(CtrlExpr in D,V,Fl,P,PP) |R3],R2,_,F)
        )
    ;
        sat_nin([X nin ris(CtrlExpr in D,V,Fl,P,PP) |R1],R2,_,F)
    ).

sat_nin_cp([T nin I|R1],R2,c,F) :-           % cp: [X,Y] nin cp(...)
    nonvar(I), I = cp(A,B), T=[X,Y],
    (   sat_nin([X nin A |R1],R2,_,F) %,!
    ;
        sat_nin([Y nin B |R1],R2,_,F)
    ).
sat_nin_cp([T nin _I|R1],R2,c,F) :-          % cp: T nin cp(...)  (npair(T))
    sat_npair([npair(T)|R1],R2,_,F).


%%%%%%%%%%%%
%%%%%%%%%%%% Rewriting rules for set/interval constraints %%%%%%%%%%%%
%%%%%%%%%%%%

%%%%%%%%%%%%%%%%%%%%%% subset (subset/2)

%solved form: subset(S1,S2): mode(prover) & var(S1) & S1 \== S2 & \+nonvar_is_empty(S2) &
%                            or
%                            var(S1) & open_intv(S2)
%                            or
%                            open_intv(S1)

sat_sub([subset(S1,S2)|R1],[subset(S1,S2)|R2],Stop,nf) :-
    var(S1),                                          % subset(X,s), var X: nf-irreducible form
    \+ compute_sols,
    \+ nonvar_is_empty(S2),
    !,
    sat_step(R1,R2,Stop,nf).

sat_sub([subset(S1,S2)|R1],R2,c,F) :-                 % subset(s,s), s any aggr_term
    S1 == S2, !,
    sat_step(R1,R2,_,F).

sat_sub([subset(S1,S2)|R1],R2,c,F) :-                 % subset(s,{}), s any aggr_term  (2) (4)
    nonvar(S2), is_empty(S2),!,
    sunify(S1,{},C1),append(C1,R1,R3),
    sat_step(R3,R2,_,F).

sat_sub([subset(S1,_S2)|R1],R2,c,F) :-                % subset({},s), s any aggr_term  (1) (8)
    nonvar(S1), is_empty(S1),!,
    sat_step(R1,R2,_,F).

sat_sub([subset(S1,S2)|R1],R2,c,F) :-                 % ground case: subset(s1,s2), ground s1,s2, s1 and s2 any non-empty set_term
    ground(S1), ground(S2),
    set_term(S1), set_term(S2),!,
    g_subset(S1,S2),
    sat_step(R1,R2,_,F).

sat_sub([subset(S1,S2)|R1],R2,c,F) :-                 % subset(cp(...),int(t1,t2)), t1,t2 any integer term with t1 =< t2
    cp_term(S1),int_term(S2),!,
    sat_step([S1={}|R1],R2,_,F).
sat_sub([subset(S1,S2)|R1],R2,c,F) :-                 % subset(int(t1,t2),cp(...)), t1,t2 any integer term with t1 =< t2
    int_term(S1),cp_term(S2),!,
    sat_step([S1={}|R1],R2,_,F).

sat_sub([subset(S1,S2)|R1],[subset(S1,S2)|R2],Stop,F) :-  % subset(X,int(A,B)), X var or var-ris  (9)
    var_ris_st(S1),                                       % irreducible in both mode(solver) and mode(prover)
    nonvar(S2), open_intv(S2),!,   
    sat_step(R1,R2,Stop,F).

sat_sub([subset(S1,S2)|R1],[subset(S1,S2)|R2],Stop,F) :-  % subset(X,Y), X, Y X var or var-ris or var-cp
    %var(S1),var(S2),!,                                   % irreducible in both mode(solver) and mode(prover)
    var_ris_st(S1), var_ris_st(S2),!,
    sat_step(R1,R2,Stop,F).

sat_sub([subset(S1,S2)|R1],R2,c,f) :-                 % special case - subset(X,{.../X}), X var
    var(S1),
    nonvar(S2), S2 = _ with _,
    tail_cp(S2,TS2), samevar(S1,TS2),!,
    sat_step(R1,R2,_,f).

sat_sub([subset(S1,S2)|R1],R2,c,f) :-                 % subset(X,{...}), X var
    compute_sols,
    var(S1),
    nonvar(S2), S2 = B with X,!,
    (sunify(S1,N with X,R),
     append(R,R1,R3),
     sat_nin([X nin N,subset(N,B)|R3],R2,_,f)
    ;
     sat_nin([X nin S1,subset(S1,B)|R1],R2,_,f)
    ).
sat_sub([subset(S1,S2)|R1],R2,c,f) :-                 % subset(X,s), X var or var-ris or var-cp, s any non-empty aggr_term
    compute_sols,                                     % rewritten in mode(solver)
    var_ris_st(S1),!,
    sat_un([un(S1,S2,S2)|R1],R2,_,f).

sat_sub([subset(R,S)|R1],[subset(R,S)|R2],Stop,F) :-  % subset(X,s), X var or var-ris or var-cp, s any non-empty aggr_term  (3) (9)
    var_ris_st(R),!,                                  % irreducible in mode(prover)
    %DBG write('subset(X,s), var X'),nl,
    sat_step(R1,R2,Stop,F).

sat_sub([subset(S1,S2)|R1],R2,R,F) :-                 % subset(int(t1,t2),s2) or subset(s1,int(t1,t2)) or subset(int(t1,t2),int(u1,u2))
    (int_term(S1) -> true ; int_term(S2)),            % s1,s2 any non-empty aggr_term; t1,t2,u1,u2 any integer term with t1 =< t2 and u1 =< u2
    !,
    sat_sub_intv([subset(S1,S2)|R1],R2,R,F).

sat_sub([subset(R with X,S)|R1],R2,c,F) :-            % subset({...},X), X var or var-ris or var-cp (5)
    var_ris_st(S),!,
    sunify(S,N with X,C1),
    append(C1,R1,R3),
    sat_sub([subset(R,N with X),set(N)|R3],R2,_,F).

sat_sub([subset(S1,S2)|R1],R2,R,F) :-                 % subset(ris(...),s2) or subset(s1,ris(...)) or subset(ris(...),ris(...))
    (ris_term(S1) -> true ; ris_term(S2)),            % s1,s2 any non-empty aggr_term
    !,
    sat_sub_ris([subset(S1,S2)|R1],R2,R,F).

sat_sub([subset(S1,S2)|R1],R2,c,F) :-                 % (special cases) subset({...|X},{...|X})
    tail_cp(S1,TS1), tail_cp(S2,TS2),                 % or subset({...|X},cp({...|X},B) or subset({...|X},cp(A,{...|X})
    samevar(TS1,TS2),!,                               % or subset(cp({...|X},B),{...|X}) or subset(cp(A,{...|X}),{...|X})
    sat_un([un(S1,S2,S2)|R1],R2,_,F).

sat_sub([subset(S1,S2)|R1],R2,R,F) :-                 % subset(cp(...),s2) or subset(s1,cp(...)) or subset(cp(...),cp(...))
    (cp_term(S1) -> true ; cp_term(S2)),              % s1,s2 any non-empty aggr_term
    !,
    sat_sub_cp([subset(S1,S2)|R1],R2,R,F).

sat_sub([subset(S,T)|R1],R2,c,F) :-                   % S and T closed set: subset({...},{...})
        S = _R with X,
        T = _ with _, 
        tail(S,TS), nonvar(TS), is_empty(TS),
        tail(T,TT), nonvar(TT), is_empty(TT),!,
        sunify(S,N1 with X,C1),
        sunify(T,N2 with X,C2),
        append(C1,C2,C12),
        append(C12,R1,R3),
        sat_nin([X nin N1,X nin N2,subset(N1,N2)|R3],R2,_,F).

sat_sub([subset(R with X,S with Y)|R1],R2,c,F) :- !,
    (   sunify(X,Y,C1),                               % subset({...},{...})   (6)
        append(C1,R1,R3),
        sat_sub([subset(R,S with Y)|R3],R2,_,F)
    ;
        sat_neq([X neq Y,X in S,subset(R,S with Y)|R1],R2,_,F)
    ).

%sat_sub(_R1,_R2,_C,_F) :-                            % otherwise
%    other_aggrs(off),!,
%    throw(setlog_excpt('unexpected case in constraint subset/2')).

%%% intervals

sat_sub_intv([subset(S1,S2)|R1],R2,c,F) :-  
    int_term(S1,A,B),                     % subset(int(t1,t2),int(s1,s2)), t1,t2,s1,s2 vars or constants 
    int_term(S2,C,D),!,
    (sat_step([B < A|R1],R2,_,F)
     ;
     sat_step([C =< A, A =< B, B =< D|R1],R2,_,F)
    ).

%delayed until final_sat is called to allow the corresponding inference rule
%in global_check2 to be applied to this constraint
sat_sub_intv([subset(S1,S2)|R1],[subset(S1,S2)|R2],Stop,nf) :-     % subset(int(t1,t2),{...}), either t1 or t2 var
    int_term(S1,_,_), open_intv(S1),!, 
    sat_step(R1,R2,Stop,nf).
sat_sub_intv([subset(S1,S2)|R1],R2,c,f) :-                         % subset(int(t1,t2),{...}), either t1 or t2 var
    int_term(S1,A,B), open_intv(S1),!, 
    (sat_step([B < A|R1],R2,_,f)
     ;
     b_getval(rw_int,RWInt),
     (apply_st(RWInt,S1,S) ->
        sat_step([A =< B, subset(S,S2)|R1],R2,_,f)
      ;
        append(RWInt,[[S1,S]],RWInt_),
        b_setval(rw_int,RWInt_),
        sat_step([subset(S,S2), A =< B, subset(S,S1), size(S,K), K is B-A+1|R1],R2,_,f)
     )
    ).

sat_sub_intv([subset(S1,S2)|R1],R2,c,F) :-           % subset({...},int(t1,t2)), t1,t2 vars or constants with t1 =< t2   (10)
    nonvar(S1), S1 = A with X,!,
    nonvar(S2), S2 = int(M,N),
    sat_step([integer(X),M =< X,X =< N,subset(A,S2),set(A)|R1],R2,_,F).
sat_sub_intv([subset(S1,S2)|R1],R2,R,F) :-           % subset(ris(...),int(t1,t2)), t1,t2 any integer term with t1 =< t2
    ris_term(S1),!,
    sat_sub_ris([subset(S1,S2)|R1],R2,R,F).
sat_sub_intv([subset(I,I2)|R1],R2,R,F) :-            % subset(int(l,h),s), int(l,h) non-empty closed interval
    closed_intv(I,_,_),!,
    sat_sub_cint([subset(I,I2)|R1],R2,R,F).
%sat_sub_intv(_R1,_R2,_C,_F) :-                      % otherwise
%    throw(setlog_excpt('unexpected case in constraint subset/2')).

%sat_sub_cint([subset(I,I2)|R1],R2,c,F) :-           % subset(int(l1,h1),int(l2,h2))
%    I=int(L,H), closed_intv(I2,L2,H2),!,
%    L2 =< L, H2 >= H,
%    sat_step(R1,R2,_,F).
sat_sub_cint([subset(I,S2)|R1],R2,c,F) :-            % subset(int(l,l),s), s any agg_term (no interval)
    I=int(L,H), L==H, !,
    sat_in([L in S2|R1],R2,_,F).
sat_sub_cint([subset(I,S2)|R1],R2,c,F) :-            % subset(int(l,h),s), s any agg_term (no interval)
    I = int(L,H),
    L1 is L + 1,
    sat_in([L in S2,subset(int(L1,H),S2)|R1],R2,_,F).

%%% RIS

sat_sub_ris([subset(S1,S2)|R1],R2,c,F) :-            % subset(ris(...),s), s any non-empty aggr_term (including RIS; no intv)
    ris_term(S1),!,
    sat_un([un(S1,S2,S2)|R1],R2,_,F).

sat_sub_ris([subset(S1,S2)|R1],R2,c,F) :-            % special rule for RIS-RUQ
    ris_term(S2,ris(CE_Dom,V,Fl,P,PP)),              % subset(s,ris(X in s,V,F,X,PP)), s any non-empty aggr_term (including RIS)
    CE_Dom = (CtrlExpr in Dom),
    CtrlExpr == P,
    nonvar(S1),
    S1 == Dom, !,
    %write('****37****'),nl,
    ctrl_expr(CtrlExpr,V,LV,CtrlExprNew),
        get_rest(Dom,CtrlExprNew,A,CNS),
    (nonvar(CNS),!,
     append(CNS,R1,R3),
     chvar(LV,[],_Vars,[Fl,P,PP,CtrlExpr],[],_VarsNew,[FlNew,PNew,PPNew,CtrlExprNew]),
     %%%%%find_corr_list(CtrlExpr,CtrlExprNew,Vars,VarsNew),
     get_preconditions(PPNew,PosPre,_),
     %
     solve_expression(Z,PNew),
     conj_append(PosPre,FlNew,PreFlNew),
     mk_atomic_constraint(PreFlNew,FlNewD),
     mk_atomic_constraint(PPNew,PPNewD),
     %
     CtrlExprNew = Z,
      sat_step([FlNewD,PPNewD,subset(A,ris(CtrlExpr in A,V,Fl,CtrlExpr,PP))|R3],R2,_,F)
     ;
      sat_sub([subset(S1,ris(CtrlExpr in A,V,Fl,CtrlExpr,PP))|R1],R2,_,F)
     ).

sat_sub_ris([subset(S1,S2)|R1],R2,c,F) :-            % subset({...},ris(...))
    ris_term(S2),!,
    sat_un([un(S1,S2,S2)|R1],R2,_,F).

%sat_sub_ris(_R1,_R2,_C,_F) :-                       % otherwise
%    throw(setlog_excpt('unexpected case in constraint subset/2')).

%%% CP

sat_sub_cp([subset(S1,S2)|R1],R2,c,F) :-             % subset(cp(...),s), s any non-empty aggr_term (including CP; no intv, no RIS)
    S1 = cp(_,_),!,
    sat_un([un(S1,S2,S2)|R1],R2,_,F).

sat_sub_cp([subset(R with X,S)|R1],R2,c,F) :-        % subset({...},cp(...))
    nonvar(S),S = cp(_,_),!,
    sat_in([X in S,subset(R,S)|R1],R2,_,F).

%sat_sub_cp(_R1,_R2,_C,_F) :-                        % otherwise
%    throw(setlog_excpt('unexpected case in constraint subset/2')).


%%%%%%%%%%%%%%%%%%%%%% strict subset (ssubset/2)

sat_ssub([ssubset(S1,S2)|R1],R2,c,F) :-
    sat_step([subset(S1,S2),S1 neq S2|R1],R2,_,F).


%%%%%%%%%%%%%%%%%%%%%% intersection (inters/3)

%solved form: inters(S1,S2,S3): (mode(prover) & one_var(S1,S2) or mode(solver) & var(S1) & var(S2)) &
%                               var(S3) &
%                               S1 \== S2 & \+nonvar_is_empty(S1) & \+nonvar_is_empty(S2)

sat_inters([inters(S1,S2,S3)|R1],[inters(S1,S2,S3)|R2],Stop,nf) :-  % inters(S1,S2,S3) nf-irreducible form
    one_var(S1,S2),var(S3),!,
    sat_step(R1,R2,Stop,nf).

sat_inters([inters(S1,S2,S3)|R1],R2,c,F) :-      % inters(S1,S1,S3), var(S1)
    var(S1), var(S2), S1 == S2,!,
    S3 = S1,
    sat_step(R1,R2,_,F).
sat_inters([inters(S1,S2,S3)|R1],R2,c,F) :-      % inters(s1,s1,S3), s1 any term, var(S3)
    var(S3), S1 == S2,!,
    S3 = S1,
    sat_step(R1,R2,_,F).

sat_inters([inters(_S1,S2,S3)|R1],R2,c,F) :-     % empty-set/empty-interval:
    nonvar(S2), is_empty(S2),!,                  % (case i) inters(S1,{},S3)
    sunify(S3,{},C),
    append(C,R1,R3),
    sat_step(R3,R2,_,F).
sat_inters([inters(S1,_S2,S3)|R1],R2,c,F) :-     % (case ii) inters({},S2,S3)
    nonvar(S1), is_empty(S1),!,
    sunify(S3,{},C),
    append(C,R1,R3),
    sat_step(R3,R2,_,F).
sat_inters([inters(S1,S2,S3)|R1],R2,c,F) :-      % (case iii) inters(S1,S2,{})
    nonvar(S3), is_empty(S3),!,
    sat_step([disj(S1,S2)|R1],R2,_,F).
sat_inters([inters(S1,S2,S3)|R1],[inters(S1,S2,S3)|R2],Stop,F) :-  % inters(S1,S2,S3), S1, S2, S3 var: irreducible form
    var(S1),var(S2),var(S3),!,
    sat_step(R1,R2,Stop,F).

sat_inters([inters(S1,S2,S3)|R1],R2,c,F) :-      % inters(S1,S2,S3), S2 and S3 var (S1 nonvar)
    var(S3),var(S2),!,
    sat_inters([inters(S2,S1,S3)|R1],R2,_,F).

sat_inters([inters(S1,S2,S3)|R1],R2,c,f) :-      % special case - inters(S1,{.../S1},S3), S3 and S1 var - mode(solver)
    compute_sols,
    var(S3),var(S1),
    nonvar(S2), S2 = _ with _,
    tail(S2,TS2), samevar(S1,TS2),!,
    sat_un([un(D,S3,S1),un(E,S3,S2),disj(D,E),set(D),set(E)|R1],R2,_,f).

sat_inters([inters(S1,S2,S3)|R1],R2,c,f) :-      % inters(S1,{...},S3), S3 and S1 var - mode(solver)
    compute_sols,
    var(S3),var(S1),nonvar(S2),S2=B with X,!,
    (sunify(S1,N with X,R),
     sunify(S3,N1 with X,RR),
     append(R,RR,RRR),append(RRR,R1,R3),
     sat_nin([X nin N,X nin N1,inters(N,B,N1)|R3],R2,_,f)
    ;
     sat_nin([X nin S1,inters(S1,B,S3)|R1],R2,_,f)
    ).
sat_inters([inters(S1,S2,S3)|R1],R2,c,f) :-      % inters(S1,S2,S3), S3 and S1 var, S2 any nonvar non-set aggr. - mode(solver)
    compute_sols,
    var(S3),var(S1),nonvar(S2),!,
    sat_un([un(D,S3,S1),un(E,S3,S2),disj(D,E),set(D),set(E)|R1],R2,_,f).

sat_inters([inters(S1,S2,S3)|R1],R2,c,f) :-      % inters(S1,S2,S3), S3 and S1 var, S2 open interval
    var(S3),var(S1),open_intv(S2),!,
    sat_un([un(D,S3,S1),un(E,S3,S2),disj(D,E),set(D),set(E)|R1],R2,_,f).

sat_inters([inters(S1,S2,S3)|R1],[inters(S1,S2,S3)|R2],Stop,F) :-  % inters(S1,S2,S3), S3 and S1 var: irreducible form
    var(S3),var(S1),!,                                             % mode(prover)
    sat_step(R1,R2,Stop,F).

sat_inters([inters(I1,I2,S3)|R1],R2,R,F) :-      % inters(int(a,b),int(c,d),t),
    nonvar(I1), I1=int(_,_),
    nonvar(I2), I2=int(_,_),!,
    sat_inters_int([inters(I1,I2,S3)|R1],R2,R,F).

sat_inters([inters(S1,S2,S3)|R1],R2,c,F) :-      % inters(r,s,t) and either r or s or t are CP
    (nonvar(S1), S1 = cp(_,_),!
     ;
     nonvar(S2), S2 = cp(_,_),!
     ;
     nonvar(S3), S3 = cp(_,_)
    ),!,
    sat_un([un(D,S3,S1),un(E,S3,S2),disj(D,E),set(D),set(E)|R1],R2,_,F).

sat_inters([inters(S1,S2,S3)|R1],R2,c,F) :-      % ground set: inters({...},{...},t)
    ground(S1), ground(S2),
    set_term(S1), set_term(S2),!,
    g_inters(S1,S2,S1_2),
    sunify(S1_2,S3,C),
    append(C,R1,R3),
    sat_step(R3,R2,_,F).

sat_inters([inters(S1,S2,S3)|R1],R2,c,F) :-      % S3 closed set: inters(t1,t2,{...})
    nonvar(S3), S3 = R with X, 
    tail(S3,TR), nonvar(TR), is_empty(TR),!,   
    sunify(S1,N1 with X,C1),
    sunify(S2,N2 with X,C2),
    append(C1,C2,C12),
    append(C12,R1,R3),
    sat_step([X nin N1, X nin N2, inters(N1,N2,R),set(N1),set(N2)|R3],R2,_,F).

sat_inters([inters(S1,S2,S3)|R1],R2,c,F) :-      % inters(S1,S2,S3), S3 any term, S1 and S2 not-var - special case
    nonvar(S1),tail(S1,TS1),
    nonvar(S2),tail(S2,TS2),
    tail(S3,TS3),
    samevar3(TS1,TS2,TS3),!,
    sat_un([un(D,S3,S1),un(E,S3,S2),disj(D,E),set(D),set(E)|R1],R2,_,F).

sat_inters([inters(S1,S2,S3)|R1],R2,c,F) :-      % inters(S1,S2,S3), S3 var, both S1 and S2 not-var
    nonvar(S1),
    nonvar(S2), S2 = RS2 with X,
    var(S3),!,
    (S3 = RS3 with X,
     sat_in([X in S1,inters(S1,RS2,RS3),set(RS2),set(RS3)|R1],R2,_,F)
     ;
     sat_nin([X nin S1,inters(S1,RS2,S3),set(RS2)|R1],R2,_,F)
    ).

sat_inters([inters(S1,S2,S3)|R1],R2,c,F) :-       % inters(S1,S2,S3), S3 not-var, both S1 and S2 not-var
    nonvar(S1),                                   % S2 set term, S1, S3 either set or interval
    nonvar(S2), S2 = _RS2 with _X,
    nonvar(S3),!,
    sat_inters([inters(S1,S2,SRes),SRes=S3|R1],R2,_,F).
sat_inters([inters(S1,S2,S3)|R1],R2,c,F) :-       % inters(S1,S2,S3), S3 not-var, both S1 and S2 not-var
    nonvar(S2),                                   % S1 set term, S2,S3 either set or interval
    nonvar(S1), S1 = _RS1 with _X,!,
    sat_inters([inters(S2,S1,S3)|R1],R2,_,F).

sat_inters([inters(S1,S2,S3)|R1],[inters(S1,S2,S3)|R2],Stop,nf) :-  % inters(S1,S2,S3), either S1 or S2 var
    one_var(S1,S2),!,                                               % delayed until final_sat is called
    sat_step(R1,R2,Stop,nf).

sat_inters([inters(S1,S2,S3)|R1],R2,c,f) :-       % inters(S1,S2,S3), S1 and S2 var, S3 not-var (final mode only)   
    var(S1), var(S2),
    nonvar(S3),S3 = N3 with X,!,
    S1 = N1 with X,
    S2 = N2 with X,
    sat_inters([inters(N1,N2,N3),set(N1),set(N2),set(N3)|R1],R2,_,f).
sat_inters([inters(S1,S2,S3)|R1],R2,c,f) :-       % inters(S1,S2,S3), either S1 or S2 var, S3 not-var - special case
    one_var(S1,S2),                               % (final mode only)
    nonvar(S3),
    tail(S3,TS3), tail(S2,TS2), tail(S1,TS1),
    samevar3(TS1,TS2,TS3),!,
    sat_un([un(D,S3,S1),un(E,S3,S2),disj(D,E),set(D),set(E)|R1],R2,_,f).
sat_inters([inters(S1,S2,S3)|R1],R2,c,f) :-       % inters(S1,S2,{...}), S1 var (final mode only) 
    var(S1),
    nonvar(S3),S3 = N3 with X,!,
    S1 = N1 with X,
    sunify(S2,N2 with X,C1),
    append(C1,R1,R3),
    sat_nin([X nin N2,inters(N1,N2,N3),set(N1),set(N2),set(N3)|R3],R2,_,f).
sat_inters([inters(S1,S2,S3)|R1],R2,c,f) :-       % inters(S1,S2,{...}), S2 var  
    var(S2),
    nonvar(S3),S3 = N3 with X,!,
    sunify(S1,N1 with X,C1),
    S2 = N2 with X,
    append(C1,R1,R3),
    sat_nin([X nin N1,inters(N1,N2,N3),set(N1),set(N2),set(N3)|R3],R2,_,f).
sat_inters([inters(S1,S2,S3)|R1],R2,c,f) :-       % inters(S1,S2,S3), either S1 or S2 var, S3 any term (other cases)
    one_var(S1,S2),!,
    sat_un([un(D,S3,S1),un(E,S3,S2),disj(D,E),set(D),set(E)|R1],R2,_,f).

sat_inters([inters(S1,S2,S3)|R1],R2,c,F) :-       % inters(r,s,t) and either r or s or t are RIS
    (ris_term(S1),! ; ris_term(S2),! ; ris_term(S3)),!,
    sat_un([un(D,S3,S1),un(E,S3,S2),disj(D,E),set(D),set(E)|R1],R2,_,F).

sat_inters_int([inters(I1,I2,S)|R1],R2,c,F) :-    % inters(int(a,b),int(c,d),S), 
    nonvar(I1), I1 = int(A,B),
    nonvar(I2), I2 = int(C,D),!,
    (sat_step([D < C, S = {}|R1],R2,_,F)
     ;
     sat_step([D < A, S = {}|R1],R2,_,F)
     ;
     sat_step([B < C, S = {}|R1],R2,_,F)
     ;
     sat_step([B < A, S = {}|R1],R2,_,F)
     ;
     sat_step([A =< C, C =< B, B =< D, S = int(C,B)|R1],R2,_,F)
     ;
     sat_step([C =< A, A =< D, D =< B, S = int(A,D)|R1],R2,_,F)
     ;
     sat_step([A =< B, C =< D, A < C, D < B, S = int(C,D)|R1],R2,_,F)
     ;
     sat_step([A =< B, C =< D, C < A, B < D, S = int(A,B)|R1],R2,_,F)
    ).

%%%%%%%%%%%%%%%%%%%%%% union (un/3)

%solved form: un(X,Y,Z): var_st(X) & var_st(Y) & var_st(Z) & X \== Y
%                        or
%                        var_ris(X) & var_ris(Y) & var_ris(Z) & X \== Y
%sat_un([un(X,Y,Z)|R1],[un(X,Y,Z)|R2],Stop,nf) :-     % un(X,Y,Z) (nf-irreducible form)
%         var(X),var(Y),var(Z),!,
%         sat_step(R1,R2,Stop,nf).

sat_un([un(S1,S2,T)|R1],R2,c,F) :-                    % un(s,s,t)   [rule U_1]
    S1==S2,!,                                         % (includes un({},{},t))
    sunify(S1,T,C),
    append(C,R1,R3),
    sat_step(R3,R2,_,F).
sat_un([un(X,Y,Z)|R1],R2,c,F) :-                      % un(Y,X,Z), var(X),var(Y),var(Z) --> un(X,Y,Z)
    var(X),var(Y),var(Z),
    X @> Y,!,
    sat_un([un(Y,X,Z)|R1],R2,_,F).

sat_un([un(X,Y,Z)|R1],[un(X,Y,Z)|R2],Stop,F) :-       % un(X,Y,Z), var_st(X),var_st(Y),var_st(Z) (irreducible form)
    var_st(X), var_st(Y), var_st(Z),!,
    sat_step(R1,R2,Stop,F).
sat_un([un(X,Y,Z)|R1],[un(X,Y,Z)|R2],Stop,F) :-       % un(X,Y,Z), var_ris(X),var_ris(Y),var_ris(Z) (irreducible form)
    var_ris(X), var_ris(Y), var_ris(Z),!,
    sat_step(R1,R2,Stop,F).

sat_un([un(T1,T2,S)|R1],R2,c,F) :-                    % un({},s,t)   [rule U_3]
    nonvar(T1), is_empty(T1),!,
    sunify(S,T2,C),
    append(C,R1,R3),
    sat_step(R3,R2,_,F).
sat_un([un(T1,T2,S)|R1],R2,c,F) :-                    % un(t,{},s)   [rule U_4]
    nonvar(T2), is_empty(T2),!,
    sunify(S,T1,C),
    append(C,R1,R3),
    sat_step(R3,R2,_,F).
sat_un([un(T1,T2,T3)|R1],R2,c,F) :-                   % un(s,t,{})   [rule U_2]
    nonvar(T3), is_empty(T3),!,
    unify_empty(T1,C1),
    unify_empty(T2,C2),
    append(C1,C2,C12), append(C12,R1,R3),
    sat_step(R3,R2,_,F).

sat_un([un(X,Y,Z)|R1],R2,c,F) :-                % un(r,s,t) not in solved form, and either r or s or t is a CP
    special_cp3(X,Y,Z,TZ,A,B),!,                % and either r or s has the same tail of t and one of is a CP and
    %write('unCP special - e.g. un(cp({X/A},B),Y,{Z/B})'),nl,  % the other is a non-CP term; e.g. un(cp({X/A},B),C,{Y/A}),
    (TZ={} ; A={} ; B={}),                      % un(cp({X/A},B),cp(C,D),{Y/A}), un(cp({X/A},{Y/B}),C,A),
    sat_un([un(X,Y,Z)|R1],R2,_,F).              % un(A,{X/B},cp({Y/A},C)), un({X/A},B,cp({Y/A},C)) .

sat_un([un(S1,S2,T)|R1],R2,R,F) :-                      % un(r,s,t) and either r or s or t are non-var CP, i.e.,
    (nonvar(S1), S1=cp(A,B), \+var_st(A),\+var_st(B),!  % un(cp(A,B),t1,t2), un(t1,cp(A,B),t1), un(t1,t2,cp(A,B))
     ;                                                  % and both A and B are non-variable terms, and t1, t2 any terms
     nonvar(S2), S2=cp(A,B), \+var_st(A),\+var_st(B),!  % (including CP)
     ;
     nonvar(T), T=cp(A,B), \+var_st(A),\+var_st(B)
    ),!,
    %write('unCP - un(r,s,t) and r or s or t are non-var CP'),nl,
    gcp_to_set(S1,SS1), gcp_to_set(S2,SS2), gcp_to_set(T,TT),
    sat_un_cp([un(SS1,SS2,TT)|R1],R2,R,F).

sat_un([un(I1,I2,S)|R1],R2,R,F) :-                   % un(r,s,t) and either r or s or t are not-empty intervals
    (nonvar(I1), I1=int(_,_),!
     ;
     nonvar(I2), I2=int(_,_),!
     ;
     nonvar(S), S=int(_,_)
    ),!,
    %write('unIntv - un(r,s,t) and r or s or t are not-empty intervals'),nl,
    sat_un_int([un(I1,I2,S)|R1],R2,R,F).

sat_un([un(S1,S2,T)|R1],R2,R,F) :-
    (ris_term(S1,ris(_ in Dom,_,_,_,_)), nonvar_ris(Dom),!
     ;
     ris_term(S2,ris(_ in Dom,_,_,_,_)), nonvar_ris(Dom),!
     ;
     ris_term(T,ris(_ in Dom,_,_,_,_)), nonvar_ris(Dom)
    ),!,
    %write('unRIS - un(r,s,t) and r or s or t are non-var RIS'),nl,
    sat_un_ris([un(S1,S2,T)|R1],R2,R,F).

sat_un([un(S1,S2,S3)|R1],R2,c,F) :-                   % un({.../R},s2,{.../R}) or un(s1,{.../R},{.../R}) (special cases)
         nonvar(S3), S3=_ with T1,
         tail(S1,TS1), tail(S2,TS2), tail(S3,TS3),
         %tail2(S1,TS1), tail2(S2,TS2), tail2(S3,TS3),
         (samevar(TS3,TS1,TS2),! ; samevarcp(TS3,TS1,TS2)),!,
         %write('unSet special - un({.../R},s2,{.../R}) or un(s1,{.../R},{.../R})'),nl,
         sunify(N with T1,S3,C1),
         ( sunify(N1 with T1,S1,C2),                               % (i)
           append(C1,C2,C3),
           R = [T1 nin N,T1 nin N1,T1 nin S2,set(N1),set(N),un(N1,S2,N)|C3]
         ;
           sunify(N1 with T1,S2,C2),                               % (ii)
           append(C1,C2,C3),
           R = [T1 nin N,T1 nin N1,T1 nin S1,set(N1),set(N),un(S1,N1,N)|C3]
         ;
           sunify(N1 with T1,S1,C21), sunify(N2 with T1,S2,C22),   % (iii)
           append(C21,C22,C2), append(C1,C2,C3),
           R = [T1 nin N,T1 nin N1,T1 nin N2,set(N1),set(N2),set(N),un(N1,N2,N)|C3]
         ),
         append(R,R1,R3),
         sat_nin(R3,R2,_,F).

sat_un([un(S1,S2,S3)|R1],R2,c,F) :-            % un(s1,s2,{...}) s1 or s2 variable; un_fe
         (var(S1) -> true ; var(S2)),           
         nonvar(S3), S3 = _ with _,                      
         b_getval(smode,prover(Strategies)),   % and the solving mode is prover([un_fe,...])          
         member(un_fe,Strategies),!,
         sat_step([foreach(X in S3, [], X in S1 or X in S2, true),
                   foreach(X in S1, [], X in S3, true),
                   foreach(X in S2, [], X in S3, true) | R1],R2,_,F).

sat_un([un(S1,S2,S3)|R1],R2,c,F) :-            % un(s1,s2,{...})  [rule U_7]
         nonvar(S3), S3=_ with T1,!,
         final_sat([N with T1=S3,T1 nin N],C1),
         %write('unSet - un(s1,s2,{...})'),nl,
         ( sunify(S1,N1 with T1,C2),                             % (i)
           append(C1,C2,C20),
           R = [T1 nin N1, set(N1),set(N), un(N1,S2,N)|C20]
         ;
           sunify(S2,N1 with T1,C2),                             % (ii)
           append(C1,C2,C20),
           R = [T1 nin N1, set(N1),set(N), un(S1,N1,N)|C20]
         ;
           sunify(S1,N1 with T1,C21), sunify(S2,N2 with T1,C22), % (iii)
           append(C1,C21,C2), append(C2,C22,C20),
           R = [T1 nin N1,T1 nin N2, set(N1),set(N2),set(N), un(N1,N2,N)|C20]
         ),
         append(R,R1,R3),
         sat_nin(R3,R2,_,F).

sat_un([un(S,T,X)|R1],R2,R,F) :-                      % un(s1,s2,X) (X var)
         var(X),!,
         %write('unSet - un(s1,s2,X) (X var)'),nl,
         sat_un_v([un(S,T,X)|R1],R2,R,F).
sat_un([un(S,T,X)|R1],R2,R,F) :-                      % un(s1,s2,X) (X variable-cp)
         nonvar(X), var_st(X),!,
         %write('unCP - un(s1,s2,X) (X variable-cp)'),nl,
         sat_un_vcp([un(S,T,X)|R1],R2,R,F).
sat_un([un(S,T,X)|R1],R2,R,F) :-                      % un(s1,s2,X) (X variable-ris)
         nonvar(X), var_ris(X),!,
         %write('unRIS - un(s1,s2,X) (X variable-ris)'),nl,
         sat_un_vris([un(S,T,X)|R1],R2,R,F).

%%% un(s1,s2,X) (X var)

sat_un_v([un(S,T,X)|R1],R2,R,F) :-                    % un({...},s2,X) (bounded set)
    bounded(S),
    occur_check(X,S), occur_check(X,T),!,
    %write('---unSet - un(s1,s2,X), s1 bounded set'),nl,
    sat_un_s([un(S,T,X)|R1],R2,R,F).
sat_un_v([un(S,T,X)|R1],R2,R,F) :-                    % un(s1,{...},X) (bounded set)
    bounded(T),
    occur_check(X,T), occur_check(X,S),!,
    %write('---unSet - un(s1,s2,X), s2 bounded set'),nl,
    sat_un_t([un(S,T,X)|R1],R2,R,F).
sat_un_v([un(S,T,X)|R1],R2,c,F) :-                    % un({...|X},t,X) (special case)
    nonvar(S),
    tail(S,TS),samevar(TS,X),  %%%!,
    %write('---unSet special - un({...|X},t,X)'),nl,
    replace_tail(S,N,NewS),
    !,
    (   samevar(TS,T) ->
        sat_eq([X=NewS,set(N)|R1],R2,_,F)             % un({...|X},X,X)
    ;
        sat_eq([X=NewS,un(T,N,N),set(N)|R1],R2,_,F)
    ).
sat_un_v([un(S,T,X)|R1],R2,c,F) :-                    % un(s,{...|X},X) (special case)
    nonvar(T),
    tail(T,TT),samevar(TT,X),
    %write('---unSet special - un(s,{...|X},X)'),nl,
    replace_tail(T,N,NewT),
    !,
    (   samevar(TT,S) ->
        sat_eq([X=NewT,set(N)|R1],R2,_,F)             % un(X,{...|X},X)
    ;
        sat_eq([X=NewT,un(S,N,N),set(N)|R1],R2,_,F)
    ).
sat_un_v([un(S,T,X)|R1],[un(S,T,X)|R2],Stop,nf) :- !, % delayed until final_sat is called
    sat_step(R1,R2,Stop,nf).                           
sat_un_v([un(S,T,X)|R1],R2,c,f) :-                    % un({...},s,X)  [rule U_5] (final mode only)
    nonvar(S), S = N1 with T1,!,
    %write('---unSet - un({.../R},s,X)'),nl,
    occur_check(X,S), novar_occur_check(X,T),
    X = N with T1,
    sat_un([un(N1,T,N),set(N),set(N1)|R1],R2,_,f).
sat_un_v([un(T,S,X)|R1],R2,c,f) :-                    % un(t,{...},X) --> un({...},t,X) [rule U_6]
    nonvar(S), S=_T2 with _T1,!,
    %write('---unSet - un(t,{.../S},X)'),nl,
    sat_un([un(S,T,X)|R1],R2,_,f).

sat_un_s([un(S,T,X)|R1],R2,c,F) :-                    % un({...},s2,X) (bounded set case)
    g_union(S,T,X),
    sat_step(R1,R2,_,F).
sat_un_t([un(S,T,X)|R1],R2,c,F) :-                    % un(s1,{...},X) (bounded set case)
    g_union(T,S,X),
    sat_step(R1,R2,_,F).

%%% un(s1,s2,X) (X variable-cp)

sat_un_vcp([un(S,T,X)|R1],R2,c,F) :-                  % un({.../S},T,cp(A,B)), and either A or B are variables
    nonvar(S), S = N1 with T1, T1 = [A1,B1],!,
    %write('---unCP - un({.../S},T,cp(A,B)), and A or B are vars'),nl,
    ( not_cp(T),!,                              % un({.../S},T,cp(A,B)), not_cp(T)
      %write('------unCP - un({.../S},T,cp(A,B)), not_cp(T)'),nl,
      sat_eq([X = N with [A1,B1],
                un(N1,T,N),
                set(N),set(N1)|R1],R2,_,F)
    ;
      nonvar(X), X = cp(A,B), A == B, T == X,!,       % un({.../S},cp(A,A),cp(A,A))
      %write('------unCP - un({.../S},cp(A,A),cp(A,A))'),nl,
      sunify(A,N with A1 with B1,CA),append(CA,R1,R3),
      sunify(N2,N3 with [A1,A1] with [B1,A1] with [B1,B1],CN2),
      append(CN2,R3,R4),
      sat_nin([A1 nin N, B1 nin N,
                [A1,A1] nin N3, [B1,A1] nin N3, [B1,B1] nin N3,
                un(N1,N2,N2),
                delay(un(cp({} with A1,N),
                         cp({} with B1,N),N4),false),
                delay(un(N4,cp(N,N with A1 with B1),N3),false),
                set(N),rel(N1),rel(N2)|R4],R2,_,F)
    ;
      nonvar(X), X = cp(A,B),
      nonvar(T), T = cp(C,D), A == C, B == D,!, % un({.../S},cp(A,B),cp(A,B))
      %write('------unCP - un({.../S},cp(A,B),cp(A,B))'),nl,
      sunify(X,N with T1,CX),append(CX,R1,R3),
%%  sat_step([subset(N1,N),set(N),set(N1)|R3],R2,_,F)
      sat_nin([T1 nin N,un(N1,N,N),set(N),set(N1)|R3],R2,_,F)
    ;
      nonvar(T), T = cp(_,_),!,                       % un({.../S},cp(_,_),cp(A,B))
      %write('------unCP - un({.../S},cp(_,_),cp(A,B))'),nl,
      sunify(X,N with T1,CX),append(CX,R1,R3),
      sat_un([un(N1,T,N),set(N),set(N1)|R3],R2,_,F)
    ).
sat_un_vcp([un(T,S,X)|R1],R2,c,F) :-                  % un(T,{.../S},cp(A,B)) --> un({.../S},T,cp(A,B))
    nonvar(S), S=_T2 with _T1,!,
    %write('---unCP - un(T,{.../S},cp(A,B)), and A or B are vars'),nl,
    sat_un([un(S,T,X)|R1],R2,_,F).

%%% un(s1,s2,X) (X variable-ris)

sat_un_vris([un(S,T,X)|R1],R2,c,F) :-                 % un({.../R},s,X)  [rule-ris U_5]
    nonvar(S), S = _ with T1,!,
    sunify(S,N1 with T1,C1), append(C1,R1,C1R1),
    sunify(X,N with T1,C2), append(C2,C1R1,R3),
    (   sat_nin([T1 nin T, T1 nin N1, T1 nin N, un(N1,T,N), set(N), set(N1)|R3],R2,_,F)
    ;   sunify(T,N2 with T1,C3), append(C3,R3,R4),
        sat_nin([T1 nin N2, T1 nin N1, T1 nin N, un(N1,N2,N), set(N), set(N1), set(N2)|R4],R2,_,F)
    ).

sat_un_vris([un(T,S,X)|R1],R2,c,F) :-                 % un(t,{.../S},X) --> un({.../S},t,X)  [rule-ris U_6]
    nonvar(S), S = _T2 with _T1,!,
    sat_un([un(S,T,X)|R1],R2,_,F).

%%% un(r,s,t) and either r or s or t are not-empty intervals

sat_un_int([un(A,B,I3)|R1], R2, c, F) :-              % un(int(t1,t2),...,int(t1,t2))             
    nonvar(I3), open_intv(I3),
    A == I3,!,
    sat_sub([subset(B,I3)|R1],R2,_,F).
sat_un_int([un(A,B,I3)|R1], R2, c, F) :-              % un(...,int(t1,t2),int(t1,t2))            
    nonvar(I3), open_intv(I3),
    B == I3,!,
    sat_sub([subset(A,I3)|R1],R2,_,F).

sat_un_int([un(I1,I2,I3)|R1],R2,c,F) :-               % un(int(...),int(...),int(...))
    nonvar(I1), I1 = int(A,B),
    nonvar(I2), I2 = int(M,N),
    nonvar(I3), I3 = int(S,T),!,
    (sat_step([B < A, int(M,N) = int(S,T)|R1],R2,_,F) 
     ;
     sat_step([N < M, int(A,B) = int(S,T)|R1],R2,_,F) 
     ;
     sat_step([A =< B, M =< N, A =< M, M =< B+1, B =< N, S = A, T = N|R1],R2,_,F)
     ;
     sat_step([A =< B, M =< N, A =< M, M =< B+1, N < B, S = A, T = B|R1],R2,_,F)
     ;
     sat_step([A =< B, M =< N, M < A, A =< N+1, B =< N, S = M, T = N|R1],R2,_,F)
     ;
     sat_step([A =< B, M =< N, M < A, A =< N+1, N < B, S = M, T = B|R1],R2,_,F)
    ).

sat_un_int([un(A,B,C)|R1], R2, c, F) :-       % at least one is a non-interval and at least one         
    cond_int_to_set(A,A1),                    % is a closed interval
    cond_int_to_set(B,B1),
    cond_int_to_set(C,C1),
    \+((A==A1,B==B1,C==C1)),!,
    sat_un([un(A1,B1,C1) | R1],R2,_,F).

sat_un_int([un(I,S,T)|R1],R2,c,F) :-                  % un(int(...),s,t) -- s and t non interval
    nonvar(I), I = int(A,B),
    (var(S) ; nonvar(S), \+functor(S,int,2)),
    (var(T) ; nonvar(T), \+functor(T,int,2)),!,
    (sat_step([B < A, S = T|R1],R2,_,F)
     ;
     b_getval(rw_int,RWInt),
     (apply_st(RWInt,I,R) ->
        sat_step([A =< B, un(R,S,T)|R1],R2,_,F)
      ;
        append(RWInt,[[I,R]],RWInt_),
        b_setval(rw_int,RWInt_),
        sat_step([A =< B, subset(R,int(A,B)), size(R,K), K is B-A+1, un(R,S,T)|R1],R2,_,F)
     )
    ).

sat_un_int([un(S,I,T)|R1],R2,c,F) :-                  % un(s,int(...),t) -- s and t non interval
    nonvar(I), I = int(_A,_B),
    (var(S) ; nonvar(S), \+functor(S,int,2)),
    (var(T) ; nonvar(T), \+functor(T,int,2)),!,
    sat_un_int([un(I,S,T)|R1],R2,c,F).

sat_un_int([un(S,T,I)|R1],R2,c,F) :-                  % un(s,t,int(...)) -- s and t non interval
    nonvar(I), I = int(A,B),
    (var(S) ; nonvar(S), \+functor(S,int,2)),
    (var(T) ; nonvar(T), \+functor(T,int,2)),!,
    (sat_step([B < A, S = {}, T = {}|R1],R2,_,F)
     ;
     b_getval(rw_int,RWInt),
     (apply_st(RWInt,I,R) ->
        sat_step([A =< B, un(S,T,R)|R1],R2,_,F)
      ;
        append(RWInt,[[I,R]],RWInt_),
        b_setval(rw_int,RWInt_),
        sat_step([A =< B, subset(R,int(A,B)), size(R,K), K is B-A+1, un(S,T,R)|R1],R2,_,F)
     )
    ).

sat_un_int([un(I1,I2,T)|R1],R2,c,F) :-                 % un(int(...),int(...),t) -- t non interval
    nonvar(I1), I1 = int(A,B),
    nonvar(I2), I2 = int(M,N),!,
    %(var(T) ; nonvar(T), \+functor(T,int,2)),!,
    (sat_step([B < A, N < M, T = {}|R1],R2,_,F)
     ;
     sat_step([B < A, M =< N, I2 = T|R1],R2,_,F)
     ;
     sat_step([A =< B, N < M, I1 = T|R1],R2,_,F)
     ;
     b_getval(rw_int,RWInt),
     (apply_st(RWInt,I1,R) ->
        (apply_st(RWInt,I2,S) ->
           sat_step([A =< B, M =< N, un(R,S,T)|R1],R2,_,F)
         ;
           append(RWInt,[[I2,S]],RWInt_),
           b_setval(rw_int,RWInt_),
           sat_step([A =< B, M =< N, 
                     subset(S,int(M,N)), size(S,K2), K2 is N-M+1, 
                     un(R,S,T)|R1],R2,_,F)
        )
      ;
        (apply_st(RWInt,I2,S) ->
           append(RWInt,[[I1,R]],RWInt_),
           b_setval(rw_int,RWInt_),
           sat_step([A =< B, M =< N, 
                     subset(R,int(A,B)), size(R,K1), K1 is B-A+1, 
                     un(R,S,T)|R1],R2,_,F)
         ;
           append(RWInt,[[I1,R],[I2,S]],RWInt_),    %I1 \== I2 is assumed
           b_setval(rw_int,RWInt_),
           sat_step([A =< B, M =< N, 
                     subset(R,int(A,B)), size(R,K1), K1 is B-A+1, 
                     subset(S,int(M,N)), size(S,K2), K2 is N-M+1, 
                     un(R,S,T)|R1],R2,_,F)
        )
     )
    ).

sat_un_int([un(I1,T,I2)|R1],R2,c,F) :-                 % un(int(...),t,int(...)) -- t non interval
    nonvar(I1), I1 = int(A,B),
    nonvar(I2), I2 = int(M,N),!,
    %(var(T) ; nonvar(T), \+functor(T,int,2)),!,
    (sat_step([N < M, I1 = {}, T = {}|R1],R2,_,F)
     ;
     sat_step([M =< N, B < A, I2 = T|R1],R2,_,F)
     ;
     b_getval(rw_int,RWInt),
     (apply_st(RWInt,I1,R) ->
        (apply_st(RWInt,I2,S) ->
           sat_step([A =< B, M =< N, un(R,T,S)|R1],R2,_,F)
         ;
           append(RWInt,[[I2,S]],RWInt_),
           b_setval(rw_int,RWInt_),
           sat_step([A =< B, M =< N, 
                     subset(S,int(M,N)), size(S,K2), K2 is N-M+1, 
                     un(R,T,S)|R1],R2,_,F)
        )
      ;
        (apply_st(RWInt,I2,S) ->
           append(RWInt,[[I1,R]],RWInt_),
           b_setval(rw_int,RWInt_),
           sat_step([A =< B, M =< N, 
                     subset(R,int(A,B)), size(R,K1), K1 is B-A+1, 
                     un(R,T,S)|R1],R2,_,F)
         ;
           append(RWInt,[[I1,R],[I2,S]],RWInt_),       %I1 \== I2 is assumed
           b_setval(rw_int,RWInt_),
           sat_step([A =< B, M =< N, 
                     subset(R,int(A,B)), size(R,K1), K1 is B-A+1, 
                     subset(S,int(M,N)), size(S,K2), K2 is N-M+1, 
                     un(R,T,S)|R1],R2,_,F)
        )
     )
    ).

sat_un_int([un(T,I1,I2)|R1],R2,c,F) :-                 % un(t,int(...),int(...)) -- t non interval
    nonvar(I1), I1 = int(_A,_B),
    nonvar(I2), I2 = int(_M,_N),!,
    %(var(T) ; nonvar(T), \+functor(T,int,2)),!,
    sat_un_int([un(I1,T,I2)|R1],R2,c,F).

cond_int_to_set(I,S) :-
    closed_intv(I,_,_),!,
    int_to_set(I,S).
cond_int_to_set(I,I).

% apply_st(F,X,Y)
% F is a function represented as a (not empty) list of ordered pairs
% apply_st searches in a F a pair whose first component is X 
% (using ==) and returns the second component in Y.
% apply_st doesn't check that F is a function and so as
% soon as the first pair of the form [X,_] is found it terminates.
% If X is not in the domain of F, apply_st fails.

apply_st([[X1,Y1]|_],X,Y1) :-
  X1 == X,!.
apply_st([[_,_]|F],X,Y) :-
  apply_st(F,X,Y).

%%% un(r,s,t) and either r or s or t are non-var RIS

sat_un_ris([un(X,Y,Z)|R1],R2,c,F) :-
    ris_to_set_t(X,N1,Xt),
    ris_to_set_t(Y,N2,Yt),
    ris_to_set_t(Z,N3,Zt),
    ris_to_set_k(X,N1,Xk),
    ris_to_set_k(Y,N2,Yk),
    ris_to_set_k(Z,N3,Zk),
    %append([un(Xt,Yt,Zt)],Xk,UnXk),
    append([delay(un(Xt,Yt,Zt),false)],Xk,UnXk),
    append(UnXk,Yk,XYk), append(XYk,Zk,XYZk),
    append(XYZk,R1,R3),
    sat_step(R3,R2,_,F).

ris_to_set_t(X,_N,X) :-
    var_ris(X),!.
ris_to_set_t(X,_N,{}) :-
    is_empty(X),!.
ris_to_set_t(X,N,N) :-
    ris_term(X),!.
ris_to_set_t(X,_N,X).

ris_to_set_k(X,_N,[A=A]) :-
    var_ris(X),!.
ris_to_set_k(X,_N,[A=A]) :-
    is_empty(X),!.
ris_to_set_k(X,N,K) :-
    ris_term(X,ris(CE_Dom,V,Fl,P,PP)),!,
    nonvar(CE_Dom), CE_Dom = (CtrlExpr in Dom),
    nonopen_intv(Dom),
    ctrl_expr(CtrlExpr,V,LV,CtrlExprNew),          %LV = vars(CtrlExpr) + vars(V)
    get_rest(Dom,CtrlExprNew,D,CNS),               %unifies the ctrl-term with the 1st elem. d of the domain
    (   nonvar(CNS) ->
        chvar(LV,[],_Vars,[Fl,P,PP,CtrlExpr],[],_VarsNew,[FlNew,PNew,PPNew,CtrlExprNew]), %rename all "local" variables in the RIS
        %%%%%find_corr_list(CtrlExpr,CtrlExprNew,Vars,VarsNew),                    %including those in CtrlExpr

        solve_expression(Z,PNew),                  %Z is P(d)
        get_preconditions(PPNew,PosPre,NegPre),
        conj_append(PosPre,FlNew,PreFlNew),
        mk_atomic_constraint(PreFlNew,FlNewD),     %FlNewD is F(d) (dealt with as a constraint)
        mk_atomic_constraint(PPNew,PPNewD),

        (   K = [FlNewD, PPNewD, N = ris(CtrlExpr in D,V,Fl,P,PP) with Z | CNS]
        ;   negate(FlNew,NegFl),
            conj_append(PosPre,PPNew,PrePPNew),
            conj_append(PrePPNew,NegFl,PreNegFl),
            mk_atomic_constraint((PreNegFl or NegPre),NegFlD), %NegFlD is not F(d) (dealt with as a constraint)
            K = [NegFlD, N = ris(CtrlExpr in D,V,Fl,P,PP) | CNS]
        )
    ;
        K = [N = ris(CtrlExpr in D,V,Fl,P,PP)]
    ).
ris_to_set_k(_X,_N,[A=A]).


%%% un(r,s,t) and either r or s or t are non-var CP

sat_un_cp([un(X,Y,Z)|R1],R2,c,F) :-                    % un(X,Y,Z) (not_cp(X), not_cp(Y), not_cp(Z))
    not_cp(X), not_cp(Y), not_cp(Z),!,
    %write(ncp_ncp_ncp),nl,
    sat_un([un(X,Y,Z)|R1],R2,_,F).
sat_un_cp([un(X,Y,Z)|R1],R2,c,F) :-                    % un(X,cp(A,B),Z) (not_cp(X)) --> un(cp(A,B),X,Z)
    nonvar(Y), Y = cp(_,_),
    not_cp(X),!,
    %write('ncp_cp_?'),nl,
    sat_un_cp([un(Y,X,Z)|R1],R2,_,F).
sat_un_cp([un(X,Y,Z)|R1],R2,c,F) :-                    % un(cp(A,B),Y,Z) (not_cp(Y), not_cp(Z))
    nonvar(X), X = cp(_,_),
    not_cp(Y), not_cp(Z),!,
    %write(cp_ncp_ncp),nl,
    cp_to_set(X,Xt,Xu),
    append(Xu,R1,R3),
    %sat_un([un(Xt,Y,Z),set(Xt)|R3],R2,_,F).
    sat_step([delay(un(Xt,Y,Z),false),set(Xt)|R3],R2,_,F).
sat_un_cp([un(X,Y,Z)|R1],R2,c,F) :-                    % un(cp(A,B),cp(C,D),Z) (not_cp(Z))
    nonvar(X), X = cp(_,_),
    nonvar(Y), Y = cp(_,_),
    not_cp(Z),!,
    %write(cp_cp_ncp),nl,
    cp_to_set(X,Xt,Xu), cp_to_set(Y,Yt,Yu),
    append(Xu,Yu,XYu), append(XYu,R1,R3),
    sat_step([un(Xt,Yt,Z),set(Xt),set(Yt)|R3],R2,_,F).
sat_un_cp([un(X,Y,Z)|R1],R2,c,F) :-                    % un(X,Y,cp(C,D)) (not_cp(X), not_cp(Y))
    not_cp(X), not_cp(Y),
    nonvar(Z), Z = cp(_,_),!,
    %write(ncp_ncp_cp),nl,
    cp_to_set(Z,Zt,Zu),
    append(Zu,R1,R3),
    sat_un([un(X,Y,Zt),set(Zt)|R3],R2,_,F).
sat_un_cp([un(X,Y,Z)|R1],R2,c,F) :-                    % un(cp(A,B),Y,cp(C,D)) (not_cp(Y))
    nonvar(X), X = cp(_,_),
    not_cp(Y),
    nonvar(Z), Z = cp(_,_),!,
    %write(cp_ncp_cp),nl,
    cp_to_set(X,Xt,Xu),
    cp_to_set(Z,Zt,Zu),
    append(Xu,Zu,XZu), append(XZu,R1,R3),
    sat_un([un(Xt,Y,Zt),set(Xt),set(Zt)|R3],R2,_,F).
sat_un_cp([un(X,Y,Z)|R1],R2,c,F) :-                    % un(cp(A,B),cp(C,D),cp(E,F))
    nonvar(X), X = cp(_,_),
    nonvar(Y), Y = cp(_,_),
    nonvar(Z), Z = cp(_,_),!,
    %write(cp_cp_cp),nl,
    cp_to_set(X,Xt,Xu),
    cp_to_set(Y,Yt,Yu),
    cp_to_set(Z,Zt,Zu),
    append(Xu,Yu,XYu),append(XYu,Zu,XYZu),
    append(XYZu,R1,R3),
    sat_un([un(Xt,Yt,Zt),set(Xt),set(Yt),set(Zt)|R3],R2,_,F).

% Transforms the cp X into the corresponding extensional set T and
% stores in U the created constraints
cp_to_set(X,T,U) :-
    nonvar(X), X = cp(A,B),
    nonvar(A), A = cp(_,_),
    nonvar(B), B = cp(_,_),!,
    cp_to_set(A,Ta,Ua),
    cp_to_set(B,Tb,Ub),
    T = cp(Ta,Tb),
    append(Ua,Ub,U).
cp_to_set(X,T,U) :-
    nonvar(X), X = cp(A,B),
    nonvar(A), A = cp(_,_),!,
    cp_to_set(A,Ta,U),
    T = cp(Ta,B).
cp_to_set(X,T,U) :-
    nonvar(X), X = cp(A,B),
    nonvar(B), B = cp(_,_),!,
    cp_to_set(B,Tb,U),
    T = cp(A,Tb).
cp_to_set(X,T,U) :-
    cp_to_set_t(M,X,T),
    cp_to_set_u(M,X,U).

cp_to_set_t(_,X,{}) :-                  % X = cp({},_)
    nonvar(X), X = cp(A,_),
    nonvar(A), is_empty(A),!.
cp_to_set_t(_,X,{}) :-                  % X = cp(_,{})
    nonvar(X), X = cp(_,B),
    nonvar(B), is_empty(B),!.
cp_to_set_t(_,X,X) :-                   % X variable cp
    var_st(X),!.
cp_to_set_t(M,X,T) :-                   % X = cp({Ea1,Ea2/_},{Eb1,Eb2/_}) (special case, to improve efficiency)
    nonvar(X), X = cp(A,B),
    nonvar(A), A = A1 with Ea1,
    nonvar(A1), A1 = _ with Ea2,
    nonvar(B), B = B1 with Eb1,
    nonvar(B1), B1 = _ with Eb2,!,
    T = M with [Ea1,Eb1] with [Ea1,Eb2] with [Ea2,Eb1] with [Ea2,Eb2].
cp_to_set_t(M,X,T) :-                   % X = cp({Ea2/_},{Eb2/_})
    nonvar(X), X = cp(A,B),
    nonvar(A), A = _ with Ea,
    nonvar(B), B = _ with Eb,!,
    T = M with [Ea,Eb].
cp_to_set_t(_,X,X).

cp_to_set_u(M,X,[M=M]) :-               % X variable cp
    var_st(X),!.
    %write('cp_to_set_u - X variable cp'),nl.
cp_to_set_u(M,X,[M = {}]) :-            % X = cp({y},{z})
    nonvar(X), X = cp(A,B),
    nonvar(A), A = Sa with _, nonvar(Sa), is_empty(Sa),
    nonvar(B), B = Sb with _, nonvar(Sb), is_empty(Sb),!.
    %write('cp_to_set_u - X = cp({y},{z})'),nl.
cp_to_set_u(M,X,U) :-                   % X = cp({y/Sa},{z})
    nonvar(X), X = cp(A,B),
    nonvar(A), A = Sa with _,
    nonvar(B), B = Sb with _, nonvar(Sb), is_empty(Sb),!,
    %write('cp_to_set_u - X = cp({y/Sa},{z})'),nl,
    U = [M = cp(Sa,B), set(Sa)].
cp_to_set_u(M,X,U) :-                   % X = cp({y},{z/Sb})
    nonvar(X), X = cp(A,B),
    nonvar(A), A = Sa with _, nonvar(Sa), is_empty(Sa),
    nonvar(B), B = Sb with _,!,
    %write('cp_to_set_u - X = cp({y},{z/Sb})'),nl,
    U = [M = cp(A,Sb), set(Sb)].
cp_to_set_u(M,X,U) :-                   % X = cp({y1,y2/Sa},{z1,z2/Sb})
    nonvar(X), X = cp(A,B),             % (special case, to improve efficiency)
    nonvar(A), A = A1 with Ea1,
    nonvar(A1), A1 = Sa with Ea2,
    nonvar(B), B = B1 with Eb1,
    nonvar(B1), B1 = Sb with Eb2,!,
    %write('cp_to_set_u - X = cp({y1,y2/Sa},{z1,z2/Sb})'),nl,
    U = [delay(un(cp({} with Ea1,Sb),cp({} with Ea2,Sb),N1),false),
         delay(un(N1,cp(Sa,Sb with Eb1 with Eb2),M),false),
         set(Sa),set(Sb),set(N1)].
cp_to_set_u(M,X,U) :-                   % X = cp({y/Sa},{z/Sb})
    nonvar(X), X = cp(A,B),
    nonvar(A), A = Sa with Ea,
    nonvar(B), B = Sb with Eb,!,
    %write('cp_to_set_u - X = cp({y/Sa},{z/Sb})'),nl,
    U = [delay(un(cp({} with Ea,Sb),cp(Sa,Sb with Eb),M),false),
         set(Sa), set(Sb)].
cp_to_set_u(_,_,[M=M]).

% get_elem(+S,?E,?R,-C): true if
% S is a (non-variable) set term, E is an element of S,
% R is the remaining set part of S (not containing E),
% C is a (possibly empty) output constraint
%
%get_elem(S,E,R,C) :-
%    nonvar(S), S = _ with E,
%    final_sat([S = R with E, E nin R, set(R)],C).%

%%% auxiliary predicates for union

identical_two(T1,T2,A,B) :-
    (nonvar(A),T1==A,! ; nonvar(B),T1==B),
    (nonvar(A),T2==A,! ; nonvar(B),T2==B).

novar_occur_check(_X,T) :-
    var(T),
    !.
novar_occur_check(X,T) :-
    occur_check(X,T).

special_cp3(X,Y,Z,TZ,A,B) :-
    nonvar(Z), Z = cp(A,B),!,
    tail_cp(Z,TZ),
    (   not_cp(X), tail_cp(X,TX), samevar(TX,TZ) ->
        true
    ;
        not_cp(Y), tail_cp(Y,TY), samevar(TY,TZ)
    ).
special_cp3(X,Y,Z,TZ,A,B) :-
    not_cp(Z),
    tail_cp(Z,TZ),
    (   nonvar(X), X = cp(A,B), tail_cp(X,TX), samevar(TX,TZ) ->
        true
    ;
        nonvar(Y), Y = cp(A,B), tail_cp(Y,TY), samevar(TY,TZ)
    ).


%%%%%%%%%%%%%%%%%%%%%% disjointness (disj/2)

%solved form: disj(X,Y), var_st(X) & var_st(Y) & X \== Y
%
%sat_disj([disj(X,Y)|R1],[disj(X,Y)|R2],Stop,nf) :-           % disj(X,Y) (nf-irreducible form)
%        var(X), var(Y),!,
%        sat_step(R1,R2,Stop,nf).

sat_disj([disj(X,Y)|R1],R2,c,F) :-                            % disj(X,X)
    var(X), var(Y), samevar(X,Y),!,
    X = {},
    sat_step(R1,R2,_,F).
sat_disj([disj(X,Y)|R1],R2,c,F) :-                            % disj(Y,X) --> disj(X,Y)
    var(X),var(Y),
    X @> Y,!,
    sat_step([disj(Y,X)|R1],R2,_,F).
sat_disj([disj(X,Y)|R1],[disj(X,Y)|R2],Stop,F) :-             % disj(X,Y), var(X), var(Y) (irreducible form)
    var(X), var(Y),!,
    %write('disj(X,Y), var(X), var(Y)'),nl,
    sat_step(R1,R2,Stop,F).

sat_disj([disj(Set1,_)|R1],R2,c,F) :-                         % disj({},t)
    nonvar(Set1), is_empty(Set1),!,
    sat_step(R1,R2,_,F).
sat_disj([disj(_,Set2)|R1],R2,c,F) :-                         % disj(t,{})
    nonvar(Set2), is_empty(Set2),!,
    sat_step(R1,R2,_,F).

sat_disj([disj(Set1,Set2)|R1],R2,c,F) :-                      % disj({...},{...})
    nonvar(Set1), Set1 = S1 with T1,
    nonvar(Set2), Set2 = S2 with T2,!,
    sat_step([T1 neq T2,T1 nin S2,T2 nin S1,set(S1),set(S2),disj(S1,S2)|R1],R2,_,F).
sat_disj([disj(Set,X)|R1],R2,c,F) :-                          % disj({...},X)
    nonvar(Set), Set = T2 with T1,
    var(X),!,
    sat_step([T1 nin X,set(T2),disj(X,T2)|R1],R2,_,F).
sat_disj([disj(X,Set)|R1],R2,c,F) :-                          % disj(X,{...})
    nonvar(Set), Set = T2 with T1,
    var(X),!,
    sat_step([T1 nin X,set(T2),disj(X,T2)|R1],R2,_,F).

sat_disj([disj(I1,I2)|R1],R2,R,F) :-                          % disj(s,t) and either s or t is an interval
    (   nonvar(I1), I1=int(_,_) ->
        true
    ;
        nonvar(I2), I2=int(_,_)
    ),
    !,
    sat_disj_int([disj(I1,I2)|R1],R2,R,F).
sat_disj([disj(T1,T2)|R1],R2,R,F) :-                          % disj(s,t) and either s or t is a CP
    (   nonvar(T1), is_cp(T1,_,_) ->
        true
    ;
        nonvar(T2), is_cp(T2,_,_)
    ),
    !,
    sat_disj_cp([disj(T1,T2)|R1],R2,R,F).
sat_disj([disj(T1,T2)|R1],R2,R,F) :-                          % disj(s,t) and either s or t is a RIS
    (   ris_term(T1) ->
        true
    ;
        ris_term(T2)
    ),
    !,
    %write(rule(disj_ris)),nl,
    sat_disj_ris([disj(T1,T2)|R1],R2,R,F).

sat_disj_int([disj(I1,I2)|R1],R2,c,F) :-                      % disj(int(a,b),int(c,d))
    closed_intv(I1,S1,S2),
    closed_intv(I2,T1,T2),!,
    (solve_int(S2 + 1 =< T1,IntC)
     ;
     solve_int(T2 + 1 =< S1,IntC)
     ;
     solve_int(S2 + 1 =< T1,IntC1), solve_int(T2 + 1 =< S1,IntC2),
     append(IntC1,IntC2,IntC)
    ),
    append(IntC,R1,R3),
    sat_step(R3,R2,_,F).
sat_disj_int([disj(I1,Set)|R1],R2,c,F) :-                     % disj(int(a,a),t)
    closed_intv(I1,S1,S2), S1==S2, !,
    sat_step([S1 nin Set|R1],R2,_,F).
sat_disj_int([disj(I1,Set)|R1],R2,c,F) :-                     % disj(int(a,b),t)
    nonvar(I1), closed_intv(I1,S1,S2),!,
    S3 is S1 + 1,
    sat_step([S1 nin Set, disj(int(S3,S2),Set)|R1],R2,_,F).

sat_disj_int([disj(Set,I1)|R1],R2,c,F) :-                     % disj(t,int(_,_)), t var or t non-interval
    nonvar(I1), I1 = int(_,_),                                % --> disj(int(_,_),t)
    (var(Set); nonvar(Set),\+functor(Set,int,2)),!,
    sat_step([disj(I1,Set)|R1],R2,_,F).

sat_disj_int([disj(I1,I2)|R1],R2,c,F) :-                      % disj(int(A,B),int(M,N)) -- at least one variable
    nonvar(I1), I1 = int(A,B),
    nonvar(I2), I2 = int(M,N),!,
    (sat_step([B < A|R1],R2,_,F)
     ;
     sat_step([N < M|R1],R2,_,F)
     ;
     sat_step([A =< B, M =< N, B < M|R1],R2,_,F)
     ;
     sat_step([A =< B, M =< N, N < A|R1],R2,_,F)
    ).
sat_disj_int([disj(I1,Set)|R1],R2,c,F) :-                     % disj(int(_,_),X), X var
    nonvar(I1), I1 = int(A,B),
    var(Set),!,
    (sat_step([B < A|R1],R2,_,F)
     ;
     b_getval(rw_int,RWInt),
     (apply_st(RWInt,I1,S) ->
        sat_step([A =< B, disj(S,Set)|R1],R2,_,F)
      ;
        append(RWInt,[[I1,S]],RWInt_),
        b_setval(rw_int,RWInt_),
        sat_step([A =< B, subset(S,int(A,B)), size(S,K), K is B-A+1, disj(S,Set)|R1],R2,_,F)
     )
    ).
sat_disj_int([disj(I1,Set)|R1],R2,c,F) :-                     % disj(int(t1,t2),{...}) --> t1 =< t2 or t2 < t1
    nonvar(I1), I1 = int(A,B),
    nonvar(Set), Set = S with X,
    (sat_step([B < A|R1],R2,_,F)
     ;
     sat_step([A =< B, X nin I1, disj(I1,S)|R1],R2,_,F)
    ).
% TODO
% interval and cp
% interval and ris

sat_disj_cp([disj(X,Y)|R1],R2,c,F) :-                         % disj(Y,cp(...)) --> disj(cp(...),Y)
    nonvar(Y), Y = cp(_,_),
    not_cp(X),!,
    sat_disj_cp([disj(Y,X)|R1],R2,_,F).
sat_disj_cp([disj(X,Y)|R1],[disj(X,Y)|R2],Stop,F) :-          % disj(X,Y) (irreducible form)
    var_st(X), var_st(Y),!,
    sat_step(R1,R2,Stop,F).
sat_disj_cp([disj(CP,Set)|R1],R2,c,F) :-                      % disj(cp(A,B),S) and either A or B are var.
    nonvar(CP), var_st(CP),
    nonvar(Set), Set = S with E,!,
    sat_step([E nin CP, disj(CP,S), set(S) |R1],R2,_,F).
sat_disj_cp([disj(CP,Set)|R1],R2,c,F) :-                      % disj(cp(...),S), S any set term or cp
    nonvar(CP), CP = cp(A,B),
    A = A1 with Ea,
    B = B1 with Eb,
    sat_step([disj(N with [Ea,Eb],Set),
        un(cp({} with Ea,B1),cp(A1,B1 with Eb),N),
        set(N),set(A1),set(B1) |R1],R2,_,F).

sat_disj_ris([disj(X,Y)|R1],[disj(X,Y)|R2],Stop,F) :-         % disj(X,Y), var_ris(X), var_ris(Y) (irreducible form)
    var_ris(X), var_ris(Y),!,
    %write('disj(X,Y), var_ris(X), var_ris(Y)'),nl,
    sat_step(R1,R2,Stop,F).
sat_disj_ris([disj(X,Y)|R1],R2,c,F) :-                        % disj(X,ris(...)) --> disj(ris(...),X)  [rule-ris ||_5]
    ris_term(Y),
    \+ ris_term(X),!,
    sat_disj_ris([disj(Y,X)|R1],R2,_,F).
sat_disj_ris([disj(Ris,Set)|R1],R2,c,F) :-                    % disj(ris(...),{...})    [rule-ris ||_4]
    nonvar(Set), Set = T2 with T1,!,
    sat_step([T1 nin Ris,set(T2),disj(Ris,T2)|R1],R2,_,F).
sat_disj_ris([disj(I,A)|R1],[disj(I,A)|R2],Stop,nf) :-
    ris_term(I,ris(CE_Dom,_,_,_,_)),
    CE_Dom = (_ in Dom), nonvar_ris(Dom),
    open_intv(Dom),!,
    sat_step(R1,R2,Stop,nf).
sat_disj_ris([disj(I,A)|R1],R2,c,F) :-                        % disj(ris(...),A), var(A) or ris(A)  [rule-ris ||_7]
    ris_term(I,ris(CE_Dom,V,Fl,P,PP)),
    nonvar(CE_Dom), CE_Dom = (CtrlExpr in Dom), nonvar_ris(Dom),!,
    nonopen_intv(Dom),
    ctrl_expr(CtrlExpr,V,LV,CtrlExprNew),
    get_rest(Dom,CtrlExprNew,D,CNS),
    (   nonvar(CNS) ->
        append(CNS,R1,R3),
        chvar(LV,[],_Vars,[Fl,P,PP,CtrlExpr],[],_VarsNew,[FlNew,PNew,PPNew,CtrlExprNew]),
        %%%%%%find_corr_list(CtrlExpr,CtrlExprNew,Vars,VarsNew),
        solve_expression(Z,PNew),
        get_preconditions(PPNew,PosPre,NegPre),
        conj_append(PosPre,FlNew,PreFlNew),
        mk_atomic_constraint(PreFlNew,FlNewD),
        mk_atomic_constraint(PPNew,PPNewD),
        (   sat_step([FlNewD,PPNewD,Z nin A,disj(ris(CtrlExpr in D,V,Fl,P,PP),A) |R3],R2,_,F)
        ;
            negate(FlNew,NegFl),
            conj_append(PosPre,PPNew,PrePPNew),
            conj_append(PrePPNew,NegFl,PreNegFl),
            mk_atomic_constraint((PreNegFl or NegPre),NegFlD),
            sat_step([NegFlD,disj(ris(CtrlExpr in D,V,Fl,P,PP),A) |R3],R2,_,F)
        )
    ;
        sat_disj_ris([disj(ris(CtrlExpr in D,V,Fl,P,PP),A) |R1],R2,_,F)
    ).
sat_disj_ris([disj(I,A)|R1],R2,c,F) :-                        % disj(A,ris(...)), var(A) or ris(A)  [rule-ris ||_6]
    ris_term(A,ris(CE_Dom,_V,_Fl,_P,_PP)),
    nonvar(CE_Dom), CE_Dom = (_CtrlExpr in Dom), nonvar_ris(Dom),!,
    sat_disj_ris([disj(A,I)|R1],R2,_,F).


%%%%%%%%%%%%%%%%%%%%%% not union (nun/3)

sat_nun([nun(S1,S2,S3)|R1],R2,c,F) :-               % nun(s1,s2,s3)
    sat_step([N in S3,N nin S1,N nin S2|R1],R2,_,F).
sat_nun([nun(S1,_S2,S3)|R1],R2,c,F) :-              %
    sat_step([N in S1,N nin S3|R1],R2,_,F).
sat_nun([nun(_S1,S2,S3)|R1],R2,c,F) :-              %
    sat_step([N in S2,N nin S3|R1],R2,_,F).


%%%%%%%%%%%%%%%%%%%%%% not disjointness (ndisj/2)

sat_ndisj([ndisj(I1,I2)|R1],R2,c,F) :-              % ndisj(int(...),int(...))
    closed_intv(I1,S1,S2),
    closed_intv(I2,T1,T2),!,
    (   solve_int(S1 =< T1,IntC1), solve_int(T1 =< S2,IntC2),
        append(IntC1,IntC2,IntC)
    ;   solve_int(T1 =< S1,IntC1), solve_int(S1 =< T2,IntC2),
        append(IntC1,IntC2,IntC)
    ),
    append(IntC,R1,R3),
    sat_step(R3,R2,_,F).
sat_ndisj([ndisj(X,Y)|R1],R2,c,F) :-                % ndisj(X,X)
    var(X), var(Y), samevar(X,Y),!,
    sat_step([X neq {}|R1],R2,_,F).
sat_ndisj([ndisj(S,T)|R1],R2,c,F) :-                % ndisj(A,B), A,B:{...} or ris or CP
    sat_step([N in S, N in T|R1],R2,_,F).


%%%%%%%%%%%%%%%%%%%%%% set difference (diff/3)

sat_diff([diff(A,B,C)|R1],R2,c,F) :-       % diff(A,A,C)
    A == B,!,
    sunify(C,{},R),
    append(R,R1,R3),
    sat_step(R3,R2,_,F).

sat_diff([diff(A,B,C)|R1],[diff(A,B,C)|R2],Stop,F) :-   % diff(X,Y,Z), var(X),var(Y),var(Z) (irreducible form)
    var(A),var(B),var(C),!,
    sat_step(R1,R2,Stop,F).

sat_diff([diff(A,_B,C)|R1],R2,c,F) :-      % diff({},B,C)
    nonvar(A), is_empty(A),!,
    sunify(C,{},R),
    append(R,R1,R3),
    sat_step(R3,R2,_,F).

sat_diff([diff(A,B,C)|R1],R2,c,F) :-      % diff(A,{},C)
    nonvar(B), is_empty(B),!,
    sunify(C,A,R),
    append(R,R1,R3),
    sat_step(R3,R2,_,F).

sat_diff([diff(A,B,C)|R1],R2,c,F) :-      % diff(A,B,{})
    nonvar(C), is_empty(C),!,
    sat_sub([subset(A,B)|R1],R2,_,F).

sat_diff([diff(I1,I2,S3)|R1],R2,R,F) :-   % diff(int(a,b),int(c,d),t),
    nonvar(I1), I1=int(_,_),
    nonvar(I2), I2=int(_,_),!,
    sat_diff_int([diff(I1,I2,S3)|R1],R2,R,F).

sat_diff([diff(A,B,S3)|R1],R2,c,F) :-     % diff(A,B,{X/C})
     nonvar(S3), S3 = _ with X,
     compute_sols,!,
     sunify(S3,N1 with X,R0),
     sunify(A,N with X,R),
     append(R0,R1,R3),
     append(R3,R,R4),
     sat_nin([X nin N1,X nin N,X nin B,diff(N,B,N1),set(N),set(N1)|R4],R2,_,F).

sat_diff([diff(A,S2,C)|R1],R2,c,F) :-     % diff(A,{X},C)
     nonvar(S2), S2 = B with X, B=={},
     compute_sols,!,
    (sunify(A,N with X,R),
     append(R,R1,R3),
     sat_nin([X nin N,C=N,set(N)|R3],R2,_,F)
     ;
     sat_nin([X nin A,C=A|R1],R2,_,F)).

sat_diff([diff(A,B,C)|R1],R2,c,F) :-     % special case - diff(X,{.../X},C)
     var(A),
     nonvar(B), B = _ with _,
     tail(B,TB), samevar(A,TB),!,
     sat_sub([subset(C,A),un(B,C,D),subset(A,D),disj(B,C),set(D)|R1],R2,_,F).
sat_diff([diff(A,B,C)|R1],R2,c,F) :-     % special case - diff({.../X},{.../X},C)
     nonvar(A), A = _ with _,
     nonvar(B), B = _ with _,
     tail(A,TA), tail(B,TB), samevar(TA,TB),!,
     sat_sub([subset(C,A),un(B,C,D),subset(A,D),disj(B,C),set(D)|R1],R2,_,F).

sat_diff([diff(A,S2,C)|R1],R2,c,F) :-     % diff(A,{X/B},C)
     nonvar(S2), S2 = B with X,
     compute_sols,!,
     (sunify(A,N with X,R),
      append(R,R1,R3),
      sat_nin([X nin N,diff(N,B,C),set(N)|R3],R2,_,F)
      ;
      sat_nin([X nin A,diff(A,B,C)|R1],R2,_,F)
     ).

sat_diff([diff(S1,B,C)|R1],R2,c,F) :-     % diff({X/A},B,C)
     nonvar(S1), S1 = _ with X,
     compute_sols,!,
     sunify(S1,N1 with X,R0),
     append(R0,R1,R3),
     (sunify(C,N with X,R),
      append(R,R3,R4),
      sat_nin([X nin N1,X nin N,X nin B,diff(N1,B,N),set(N),set(N1)|R4],R2,_,F)
      ;
      sunify(B,N with X,R),
      append(R,R3,R4),
      sat_nin([X nin N1,X nin N,diff(N1,N,C),set(N),set(N1)|R4],R2,_,F)
     ).

sat_diff([diff(A,B,C)|R1],R2,c,F) :-       % all other cases
    sat_sub([subset(C,A), un(B,C,D), subset(A,D), disj(B,C), set(D)|R1],R2,_,F).

sat_diff_int([diff(I1,I2,S)|R1],R2,c,F) :- % diff(int(a,b),int(c,d),S)
    int_term(I1,A,B),
    int_term(I2,C,D),!,
    (sat_step([B < A, S = {}|R1],R2,_,F)
     ;
     sat_step([A =< B, D < C, S = int(A,B)|R1],R2,_,F)
     ;
     sat_step([A =< B, C =< D, B < C, S = int(A,B)|R1],R2,_,F)
     ;
     sat_step([A =< B, C =< D, D < A, S = int(A,B)|R1],R2,_,F)
     ;
     sat_step([C =< A, A =< B, B =< D, S = {}|R1],R2,_,F)
     ;
     sat_step([A =< C, C =< B, B =< D, C1 is C - 1, S = int(A,C1)|R1],R2,_,F)
     ;
     sat_step([C =< A, A =< D, D =< B, D1 is D + 1, S = int(D1,B)|R1],R2,_,F)
     ;
     sat_step([A =< C, C =< D, D =< B, 
               C1 is C - 1, D1 is D + 1, 
               un(int(A,C1),int(D1,B),S)|R1],R2,_,F)
    ).


%%%%%%%%%%%%
%%%%%%%%%%%% Rewriting rules for aggregate constraints %%%%%%%%%%%%
%%%%%%%%%%%%

%%%%%%%%%%%%%%%%%%%%%% set cardinality (size/2)

%solved form: size(S,N), var(S) & var(N)
%
sat_size([size(S,N)|R1], [solved(size(S,N),(var(S),var(N)),1)|R2],c,F) :-
    var(S),var(N),!,                           % size(S,N), var S,N (irreducible form)
    solve_int(N >= 0,IntC),
    append(IntC,R1,R3),
    sat_step(R3,R2,_,F).
sat_size([size(S,N)|R1],R2,c,F) :-             % size(s,0)
    nonvar(N), N==0,!,
    sunify(S,{},C),
    append(C,R1,R3),
    sat_step(R3,R2,_,F).
sat_size([size(I,T)|R1],R2,c,F) :-             % size(int(a,b),t), a,b constants or variables  
    nonvar(I), I = int(A,B),!,
    simple_integer_expr(T),
    (solve_int(A > B,IntC),
     append(IntC,R1,R3),
     T = 0,
     sat_step(R3,R2,_,F)
    ;
     solve_int(T > 0,IntC1),
     solve_int(T is B-A+1,IntC2),
     append(IntC1,IntC2,IntC),
     append(IntC,R1,R3),
     sat_step(R3,R2,_,F)
    ).
sat_size([size(I,T)|R1],R2,c,F) :-                  % size(cp(a,b),t)
    nonvar(I), I = cp(A,B),
    !,
    (   sat_step([T=0,A={}|R1],R2,_,F)
    ;   sat_step([T=0,B={}|R1],R2,_,F)
    ;   solve_int(T is N1*N2,IntC),
        append(IntC,R1,R3),
        sat_step([T > 0,size(A,N1),size(B,N2),integer(N1),integer(N2)|R3],R2,_,F)
    ).
sat_size([size(S,T)|R1],R2,c,F) :-                  % ground case
    ground(S),!,
    simple_integer_expr(T),
    g_size(S,T),
    sat_step(R1,R2,_,F).

sat_size([size(S,T)|R1],R2,c,F) :-                  % size(S,k), S var., k int. const. =< size_limit
    var(S),
    integer(T), size_limit(L), T =< L,!,
    solve_int(T >= 1,IntC1),
    S = R with X,
    solve_int(M is T-1,IntC2),
    append(IntC1,IntC2,IntC),
    append(IntC,R1,R3),
    sat_step([X nin R,set(R),integer(M),size(R,M)|R3],R2,_,F).

sat_size([size(S,T)|R1],[size(S,T)|R2],Stop,nf) :-  % size(S,k), S var., k nonvar
    var(S),!,                                       % delayed until final_sat is called
    sat_step(R1,R2,Stop,nf).
sat_size([size(S,T)|R1],R2,c,f) :-                  % size(S,k), S var., k nonvar (final mode only)
    var(S),
    (\+size_solver_on -> true;                    
     b_getval(smode,solver) -> true ; 
     b_getval(subset_int,true) -> true ;
     b_getval(fix_size,on) 
    ),!,                    
    integer(T),
    solve_int(T >= 1,IntC1),
    S = R with X,
    solve_int(M is T-1,IntC2),
    append(IntC1,IntC2,IntC),
    append(IntC,R1,R3),
    sat_step([X nin R,set(R),integer(M),size(R,M)|R3],R2,_,f).
sat_size([size(S,T)|R1],[size(S,T)|R2],Stop,f) :-   % size(S,k), S var., k nonvar (final mode only)
    var(S),!,                                       % (irreducible form)
    T >= 1,    
    sat_step(R1,R2,Stop,f).

sat_size([size(R with X,T)|R1],R2,c,F) :-
    simple_integer_expr(T),                         % size({...},t)
    solve_int(T >= 1,IntC1),
    solve_int(M is T-1,IntC2),
    append(IntC1,IntC2,IntC),
    append(IntC,R1,R3),
    ( 
      sat_step([X nin R,set(R),integer(M),size(R,M)|R3],R2,_,F)
    ;   
      sat_step([R=N with X,set(N),X nin N,integer(M),size(N,M)|R3],R2,_,F)
    ).

%%%%%%%%%%%%%%%%%%%%%% min of a set (smin/2)   %%%%%%%%%%%
% find the minimum M of a set S of integer numbers

sat_min([smin(S,M)|R1],R2,c,F) :-       % smin(S,M)
    %sat_in([M in S, subset(S,int(M,_))|R1],R2,_,F).
    sat_in([M in S, foreach(X in S,[],M =< X,true)|R1],R2,_,F).

%%%%%%%%%%%%%%%%%%%%%% max of a set (smax/2)  %%%%%%%%%
% find the maximum M of a set S of integer numbers

sat_max([smax(S,M)|R1],R2,c,F) :-       % smax(S,M)
    %sat_in([M in S, subset(S,int(_,M))|R1],R2,_,F).
    sat_in([M in S, foreach(X in S,[],M >= X,true)|R1],R2,_,F).

%%%%%%%% Under development - to be completed and tested
%%%%%%%%%%%%%%%%%%%%% set sum (sum/2)

sat_sum([sum(S,N)|R1],
        [solved(sum(S,N),(var(S),var(N)),1)|R2],c,F) :-   %
    var(S),var(N),!,                                % sum(S,N), var S,N (irreducible form)
    solve_int(N >= 0,IntC),
    append(IntC,R1,R3),
    sat_step(R3,R2,_,F).
%sat_sum([sum(S,0)|_R1],_R2,c,_F) :-                % sum({},t) or sum(int(a,b),t),  
%    nonvar(S),is_empty(S),!,
%    fail.
sat_sum([sum(I,T)|R1],R2,c,F) :-                    % sum(int(a,b),t), a =< b
    closed_intv(I,A,B),
    A =< B,!,
    simple_integer_expr(T),
    (int_solver(clpq) ->    
       solve_int(T is ((B*(B+1))-(A*(A-1)))/2,IntC)
    ;
       solve_int(T is ((B*(B+1))-(A*(A-1))) div 2,IntC)
    ),
    append(IntC,R1,R3),
    sat_step(R3,R2,_,F).
sat_sum([sum(S,T)|R1],R2,c,F) :-                    % ground case
    ground(S),!,
    simple_integer_expr(T),
    g_sum(S,T),
    sat_step(R1,R2,_,F).
sat_sum([sum(S,T)|R1],[sum(S,T)|R2],Stop,nf) :-   % sum(S,k), k int. const, S var.
    var(S), integer(T),!,                         % delayed until final_sat is called
    sat_step(R1,R2,Stop,nf).                      
%sat_sum([sum(S,T)|R1],[solved(sum(S,T),var(S),1)|R2],Stop,f) :-              
%    var(S), integer(T),                          % sum(S,k), k int. const, S var. (final mode only)
%    nolabel,!,                                   % if nolabel --> irreducible form
%    sat_step(R1,R2,Stop,f).
sat_sum([sum(S,T)|R1],R2,c,f) :-                  % sum(S,k), k int. const, S var. (final mode only)
    var(S), integer(T),!,
    solve_int(T >= 0,IntC1),
    sum_all(S,T,int(0,T),[],IntC2),
%    S \== {},
    append(IntC1,IntC2,IntC),
    append(IntC,R1,R3),
    sat_step(R3,R2,_,f).

sat_sum([sum(R with X,T)|R1],R2,c,nf) :-   
    integer(T),!,                                 % sum({...},k), k integer constant
    solve_int(T >= 0,IntC1),                      % delayed until final_sat is called
    add_elem_domain(R with X,T,IntC2),
    append(IntC1,IntC2,IntC),
    append(IntC,R1,R3),
    sat_step([delay(sum(R with X,T),false)|R3],R2,_,nf).

sat_sum([sum(R with X,T)|R1],[sum(R with X,T)|R2],Stop,nf) :- !,
    var(T),!,                                     % sum({...},N), N var.
    sat_step(R1,R2,Stop,nf).                      % delayed until final_sat is called

sat_sum([sum(R with X,T)|R1],R2,c,f) :-
    simple_integer_expr(T),                       % sum({...},t) (final mode only)
    simple_integer_expr(X),
    solve_int(T >= 0,IntC1),
    solve_int(X >= 0,IntC2),
    solve_int(T is M+X,IntC3),
    append(IntC1,IntC2,IntC12),
    append(IntC12,IntC3,IntC),
    append(IntC,R1,R3),
    (sat_step([integer(X),X nin R,set(R),sum(R,M)|R3],R2,_,f)
    ;
    sat_step([integer(X),R=N with X,X nin N,set(N),sum(N,M)|R3],R2,_,f) ).

sum_all({},0,_,_,[]).
sum_all(R with X,N,L,G,IntC) :-
    solve_int(X in L,IntC1),
    in_order_list(X,G,IntC2),
    append(IntC1,IntC2,IntC12),
    solve_int(N is X + M,IntC3),
    append(IntC12,IntC3,IntC123),
    sum_all(R,M,L,[X|G],IntC4),
    labeling(X),
    append(IntC123,IntC4,IntC).

in_order_list(_A,[],[]) :- !.
in_order_list(A,[B|_R],IntC) :-
    solve_int(A > B,IntC).

add_elem_domain(R,_,[]) :-
    var(R),!.
add_elem_domain(T,_,[]) :-
    is_empty(T),!.
add_elem_domain(R with A,N,IntC) :-
    solve_int(A in int(0,N),IntC1),
    add_elem_domain(R,N,IntC2),
    append(IntC1,IntC2,IntC).

%%%%%%%%%%%%%%%%%%% implementation of ground cases %%%%%%%%%%%%%%%%%%%

g_neq(T1,T2) :-
    \+ g_equal(T1,T2).

% deterministic membership (for intervals/sets/multisets/lists):
% g_member(T,A) is true if A contains T (T, A non-variable terms)
g_member(X,I) :-
    closed_intv(I,A,B),integer(X),!,
    X >= A, X =< B.
g_member(X,S) :-
    aggr_comps(S,Y,_R),
    g_equal(X,Y),!.
g_member(X,S) :-
    aggr_comps(S,_Y,R),
    g_member(X,R),!.
g_member(X,S) :-
    X=[Y1,Y2],S = cp(A,B),!,
    g_member(Y1,A),g_member(Y2,B).

g_subset(T,_) :-
    is_empty(T).
g_subset(I,S) :-
    closed_intv(I,A,A),!,
    g_member(A,S).
g_subset(I,S) :-
    closed_intv(I,A,B),!,
    g_member(A,S),
    A1 is A + 1,
    g_subset(int(A1,B),S).
g_subset(CP,S) :-
    cp_term(CP),!,
    gcp_to_set(CP,CPSet),
    g_subset(CPSet,S).
g_subset(R with X,S2) :-
    g_member(X,S2),
    g_subset(R,S2).

g_equal(T1,T2) :-
    is_empty(T1), is_empty(T2),!.
g_equal(T1,T2) :-
    T1 = T2,!.
g_equal(T1,T2) :-
    g_subset(T1,T2),
    g_subset(T2,T1).

g_union(T,S,S) :-
    is_empty(T),!.
g_union(S1 with X,S2,S3 with X) :-
    g_union(S1,S2,S3).

g_inters(T,_S,{}) :-
    is_empty(T),!.
g_inters(_S,T,{}) :-
    is_empty(T),!.
g_inters(S1 with X,S2,S3 with X) :-
    g_member(X,S2),!,
    g_inters(S1,S2,S3).
g_inters(S1 with _X,S2,S3) :-
    g_inters(S1,S2,S3).

g_size(T,0) :-
    is_empty(T),!.
g_size(int(A,B),N) :- !,
    N is B-A+1.
g_size(R with A,N) :-
    g_member(A,R),!,
    g_size(R,N).
g_size(R with _A,N) :-
    solve_int(N is M+1,_),
    g_size(R,M).

g_sum(T,0) :-
    is_empty(T),!.
g_sum(R with A,N) :-
    integer(A), A >= 0,
    g_member(A,R),!,
    g_sum(R,N).
g_sum(R with A,N) :-
    integer(A), A >= 0,
    solve_int(N is M+A,_),
    g_sum(R,M).


%%%%%%%%%%%%
%%%%%%%%%%%% Rewriting rules for type constraints %%%%%%%%%%%%
%%%%%%%%%%%%

%%%%%%%%%%%%%%%%%%%%%% set (set/1)

sat_set([set(X)|R1],[set(X)|R2],Stop,F) :-        % set(X) (irreducible form)
    var(X),!,
    sat_step(R1,R2,Stop,F).
sat_set([set(X)|R1],R2,c,F) :-                    % set({})
    X == {}, !,
    sat_step(R1,R2,_,F).
sat_set([set(X)|R1],R2,c,F) :-                    % set({...})
    X = _S with _A, !,
    sat_step(R1,R2,_,F).
sat_set([set(X)|R1],R2,c,F) :-                    % set(int(...))
    X = int(A,B),!,
    sat_step([integer(A),integer(B)|R1],R2,_,F).
sat_set([set(X)|R1],R2,c,F) :-                    % set(ris(...))
    ris_term(X,_),!,
    sat_step(R1,R2,_,F).
sat_set([set(X)|R1],R2,c,F) :-                    % set(cp(...))
    X = cp(_A,_B),!,
    sat_step(R1,R2,_,F).

%%%%%%%%%%%%%%%%%%%%%% bag (bag/1)

%sat_bag([bag(X)|R1],[bag(X)|R2],Stop,F) :-        % bag(X) (irreducible form)
%    var(X),!,
%    sat_step(R1,R2,Stop,F).
%sat_bag([bag(X)|R1],R2,c,F) :-
%    X == {}, !,
%    sat_step(R1,R2,_,F).
%sat_bag([bag(X)|R1],R2,c,F) :-
%    X = _S mwith _A,
%    sat_step(R1,R2,_,F).

%%%%%%%%%%%%%%%%%%%%%% list (list/1)

%sat_list([list(X)|R1],[list(X)|R2],Stop,F) :-     % list(X) (irreducible form)
%    var(X),!,
%    sat_step(R1,R2,Stop,F).
%sat_list([list(X)|R1],R2,c,F) :-
%    X == [], !,
%    sat_step(R1,R2,_,F).
%sat_list([list(X)|R1],R2,c,F) :-
%    X = [_A|_S],
%    sat_step(R1,R2,_,F).

%%%%%%%%%%%%%%%%%%%%%% integer (integer/1)

sat_integer([integer(X)|R1],[integer(X)|R2],Stop,F) :-  % integer(X) (irreducible form)
    var(X),!,
    sat_step(R1,R2,Stop,F).
sat_integer([integer(T)|R1],R2,c,F) :-                  % integer(t), t is an integer constant
    integer(T),
    sat_step(R1,R2,_,F).

%%%%%%%%%%%%%%%%%%%%%% not set (nset/1)

sat_nset([nset(X)|R1],[nset(X)|R2],Stop,F) :-           % nset(X) (irreducible form)
    var(X),!,
    sat_step(R1,R2,Stop,F).
sat_nset([nset(X)|_R1],_R2,c,_F) :-                     % nset({...}) or nset(int(.,.) or nset(cp(.,.) or nset(ris(...))
    aggr_term(X),!, fail.
sat_nset([nset(_X)|R1],R2,c,F) :-                       % nset(f(...))
    sat_step(R1,R2,_,F).

%%%%%%%%%%%%%%%%%%%%%% not integer (ninteger/1)

sat_ninteger([ninteger(X)|R1],[ninteger(X)|R2],Stop,F) :-  % ninteger(X) (irreducible form)
    var(X), !,
    sat_step(R1,R2,Stop,F).
sat_ninteger([ninteger(X)|R1],R2,c,F) :-
    \+ integer(X),
    sat_step(R1,R2,_,F).

%%%%%%%%%%%%
%%%%%% Rewriting rules for primitive constraints over binary relations and partial functions %%%%%%
%%%%%%%%%%%%

%%%%%%%%%%%%%%%%%%%%%% binary relation (rel/1)

sat_rel([rel(X)|R1],[rel(X)|R2],Stop,F) :-          % rel(X) (irreducible form)
    var(X),
    !,
    sat_step(R1,R2,Stop,F).
sat_rel([rel(X)|R1],R2,c,F) :-                      % rel({})
    nonvar(X),is_empty(X),!,   
    sat_step(R1,R2,_,F).
sat_rel([rel(X)|R1],R2,c,F) :-                      % rel(int(A,B)) open interval (case B < A, i.e. empty set)
    nonvar(X), open_intv(X),!,    
    X = int(M,N),                 
    sat_step([N < M|R1],R2,_,F).
sat_rel([rel(X)|R1],R2,c,F) :-                      % rel({[t1,t2],...,[t1,t2],...})
    X = S with [_A1,_A2],!,
    sat_step([rel(S)|R1],R2,_,F).
sat_rel([rel(X)|R1],R2,c,F) :-                      % rel(ris(...))
    ris_term(X,ris(_,_,_,[_A1,_A2],_)),!,
    sat_step(R1,R2,_,F).
sat_rel([rel(X)|R1],R2,c,F) :-                      % rel(cp(...))
    X = cp(_A,_B),!,
    sat_step(R1,R2,_,F).

%%%%%%%%%%%%%%%%%%%%%% partial function (pfun/1)

sat_pfun([pfun(X)|R1],R2,c,F) :-                    % pfun({})
        nonvar(X),is_empty(X),!,
        sat_step(R1,R2,_,F).
sat_pfun([pfun(X)|R1],R2,c,F) :-                    % pfun(int(A,B)) open interval (case B < A, i.e. empty set)
       nonvar(X), open_intv(X),!,    
       X = int(M,N),                 
       sat_step([N < M|R1],R2,_,F).
sat_pfun([pfun(X)|R1],[pfun(X)|R2],Stop,F) :-       % pfun(X) (irreducible form)
        var_ris_st(X),!,
        sat_step(R1,R2,Stop,F).
sat_pfun([pfun(X)|R1],R2,c,F) :-                    % pfun(F), with F closed set and dom(F) ground
        dom_all_known(X),!,
        pfun_term(X),
        sat_step(R1,R2,_,F).
sat_pfun([pfun(X)|R1],R2,c,F) :-                    % pfun(ris(_ in {_/_},...))
        ris_term(X),!,
        sunify(X,R with [A1,_A2],C1),
        not_occur(A1,R,C),
        append(C1,C,C1_C), append(C1_C,R1,R3),
        sat_step([pfun(R)|R3],R2,_,F),!.
sat_pfun([pfun(X)|R1],R2,c,F) :-                    % pfun(cp({...},{...}))
        nonvar(X), X = cp(_A,B),!,
        sunify(B,{} with _,C),
        append(C,R1,R3),
        sat_step(R3,R2,_,F).
sat_pfun([pfun(X)|R1],R2,c,F) :-                    % pfun({[...],[...],...})
        X = S with [A1,_A2],
        not_occur(A1,S,C),
        append(C,R1,R3),
        sat_step([pfun(S)|R3],R2,_,F).
sat_pfun([pfun(X)|R1],R2,c,F) :-                    % pfun({[t1,t2],...,[t1,t2],...})
        X = S with [A1,A2],
        sunify(S,R with [A1,A2],C1),
        not_occur(A1,R,C),
        append(C1,C,C1_C), append(C1_C,R1,R3),
        sat_step([pfun(R)|R3],R2,_,F).

not_occur(A,S,[comppf({} with [A,A],S,{})]) :-      % not_occur(A,R,C): true if R represents a set of pairs 
        var(S),!.                                   % and A does not occur in the domain of R (with
not_occur(A,S,[A nin S1]) :-                        % constraint C); equiv. to dompf(S,D) & A nin D
        S = cp(S1,_S2),!.
not_occur(_A,{},[]) :- !.
not_occur(A,R with [A1,_A2],[A neq A1|CR]) :- !,
        not_occur(A,R,CR).
not_occur(A,S,[comppf({} with [A,A],S,{})]) :-
        ris_term(S).

dom_all_known(R) :-
    nonvar(R), R={}, !.
dom_all_known(R with [X,_]) :-
    ground(X),
    dom_all_known(R).

%%%%%%%%%%%%%%%%%%%%%% pair (pair/1)

sat_pair([pair(X)|R1],R2,c,F) :-                   % pair([X,Y])
    X=[_,_],!,
    sat_step(R1,R2,_,F).


%%%%%%%%%%%%%%%%%%%%%% domain of a binary relation (dom/2)

sat_dom([dom(S,D)|R1],[dom(S,D)|R2],Stop,F) :-     % dom(S,D) (irreducible form)
    var(S),var(D),S\==D,!,
    sat_step(R1,R2,Stop,F).
sat_dom([dom(S,D)|R1],R2,_,F) :-                   % dom(S,D), D = int(A,B) open interval
   %%nonvar(D), D = int(M,N), open_intv(D),!,
    nonvar(D), open_intv(D),!,    
    D = int(M,N),                 
    (sat_step([N < M, S = {}|R1],R2,_,F)
    ;
     b_getval(rw_int,RWInt),
     (apply_st(RWInt,D,R) ->
         sat_step([M =< N, dom(S,R)|R1],R2,_,F)
       ;
         append(RWInt,[[D,R]],RWInt_),
         b_setval(rw_int,RWInt_),
         sat_step([M =< N, subset(R,int(M,N)), size(R,K), K is N-M+1, dom(S,R)|R1],R2,_,F)
     )
    ).

sat_dom([dom(S,D)|R1],R2,c,F) :-                   % dom({},d) 
    nonvar(S),is_empty(S),!,
    sunify(D,{},C),
    append(C,R1,R3),
    sat_step(R3,R2,_,F).
sat_dom([dom(S,D)|R1],R2,c,F) :-                   % dom(int(A,B),d) open interval (case B < A, i.e. empty set)
    nonvar(S), open_intv(S),!,    
    S = int(M,N), 
    sunify(D,{},C),
    append(C,R1,R3),               
    sat_step([N < M|R3],R2,_,F).
sat_dom([dom(S,D)|R1],R2,c,F) :-                   % dom(s,{})
    nonvar(D),is_empty(D),!,
    sunify(S,{},C),
    append(C,R1,R3),
    sat_step(R3,R2,_,F).

sat_dom([dom(S,D)|_R1],_R2,c,_F) :-                % dom(t,t), nonvar t; e.g. dom({Y/R},{Y/R}) (special case)
    nonvar(S),nonvar(D),S==D,!,
    fail.
sat_dom([dom(S,D)|R1],R2,R,F) :-                   % dom(cp(...),D) or dom(S,cp(...))
    (   nonvar(S), S = cp(_,_) ->
        true
    ;
        nonvar(D), D = cp(_,_)
    ),
    !,
    sat_dom_cp([dom(S,D)|R1],R2,R,F).
sat_dom([dom(S,D)|R1],R2,c,F) :-                   % dom(X,X) or dom({.../R},{.../R}) (special case)
    tail(S,TS),tail(D,TD),
    samevar(TS,TD),!,
    TS = {},
    sat_step([dom(S,D)|R1],R2,_,F).
sat_dom([dom(S,D)|R1],R2,c,F) :-                   % dom({...},D) or dom({...},{...}) or dom({...},int(a,b)), a and b constants
    nonvar(S), S = SR with [A1,_A2], !,
    sunify(D,DR with A1,C),
    append(C,R1,R3),
    sat_step([dom(SR,DR),rel(SR),set(DR)|R3],R2,_,F).
sat_dom([dom(S,D)|R1],R2,c,F) :-                   % dom(S,{t})  or dom(S,int(a,a)), a constant
    var(S),
    nonvar(D), singleton(D,A), !,
    sat_step([comp({} with [A,A],R,R),S = R with [A,Z],[A,Z] nin R,rel(R)|R1],R2,_,F).
sat_dom([dom(S,D)|R1],[dom(S,D)|R2],Stop,nf) :-    % dom(S,D), S var.
    var(S),!,                                      % delayed until final_sat is called
    sat_step(R1,R2,Stop,nf).                       
sat_dom([dom(S,D)|R1],R2,c,f) :-                   % dom(S,{...}) or dom(S,int(a,b)), a and b constants, S var. (final mode only)
    var(S), nonvar(D), first_rest(D,A,_DR,_) ,!,
    sunify(D,DR with A,C),
    append(C,R1,R3),
    sat_step([A nin DR,dom(S1,{} with A),dom(S2,DR),
        delay(un(S1,S2,S),false),set(DR),rel(S1),rel(S2)|R3],R2,_,f).

sat_dom_cp([dom(S,D)|R1],[dom(S,D)|R2],Stop,F) :-  % dom(S,D) (irreducible form)
    var_st(S), var_st(D),!,
    sat_step(R1,R2,Stop,F).
%sat_dom_cp([dom(S,D)|_R1],_R2,c,_F) :-             % dom(t,cp(t,B)) or dom(t,cp(A,t)), nonvar t (special case)
%   nonvar(S),                                      % not necessary
%   nonvar(D),D = cp(A,B),
%   (nonvar(A),S==A,! ; nonvar(B),S==B),!,
%   fail.
sat_dom_cp([dom(S,D)|R1],R2,c,F) :-                % dom(X,cp(X,B)) or dom({.../R},cp({.../R},B))
    nonvar(D),D = cp(A,B),                         % or dom({.../R},cp(A,{.../R})) (special case)
    tail(S,TS),
%   (tail(A,TA),samevar(TS,TA),!
%    ;
%    tail(B,TB),samevar(TS,TB)
%   ),!,
    same_tail(A,B,TS),!,
    TS = {},
    sat_step([dom(S,D)|R1],R2,_,F).
sat_dom_cp([dom(S,D)|R1],[dom(S,D)|R2],Stop,F) :-  % dom(S,D) (irreducible form)
    var_st(S), var_st(D),!,
    sat_step(R1,R2,Stop,F).
sat_dom_cp([dom(S,D)|R1],R2,c,F) :-                % dom(cp({},_),d) or dom(cp(_,{}),d)
    nonvar(S), S = cp(A,B),
    is_empty(A,B),!,
    sunify(D,{},C),
    append(C,R1,R3),
    sat_step(R3,R2,_,F).
sat_dom_cp([dom(S,D)|R1],R2,c,F) :-                % dom(s,cp({},_)) or dom(s,cp(_,{}))
    nonvar(D), D = cp(A,B),
    nonvar(A), nonvar(B), is_empty(A,B),!,
    sunify(S,{},C),
    append(C,R1,R3),
    sat_step(R3,R2,_,F).
sat_dom_cp([dom(S,D)|R1],R2,c,F) :-                % dom(s,cp(...))
    nonvar(D), D = cp(A,B),
    A = A1 with Ea, B = B1 with Eb,!,
    sat_step([dom(S,N with [Ea,Eb]),
              un(cp({} with Ea,B1),cp(A1,B1 with Eb),N),
              set(N),set(A1),set(B1) |R1],R2,_,F).
sat_dom_cp([dom(S,D)|R1],R2,c,F) :-                % dom(cp(...),d)
    nonvar(S), S = cp(A,B),
    sunify(A,D,C),
    append(C,R1,R3),
    sat_step([B neq {} | R3],R2,_,F).

is_empty(A,B) :-
    (   nonvar(A), is_empty(A) ->
        true
    ;
        nonvar(B),is_empty(B)
    ).

singleton(S,A) :-
    S = E with A, nonvar(E), is_empty(E), !.
singleton(S,A) :-
    S = int(A,A), integer(A).

%%%%%%%%%%%%%%%%%%%%%% inverse of a binary relation (inv/2)

sat_inv([inv(R,S)|R1],[inv(R,S)|R2],Stop,F) :-     % inv(X,Y) (irreducible form)
    var(R),var(S),!,
    sat_step(R1,R2,Stop,F).
sat_inv([inv(R,S)|R1],R2,c,F) :-                   % inv({},S) [rule inv_2]
    nonvar(R),is_empty(R),!,
    sunify(S,{},C),
    append(C,R1,R3),
    sat_step(R3,R2,_,F).
sat_inv([inv(R,S)|R1],R2,c,F) :-                   % inv(R,{}) [rule inv_1]
    nonvar(S),is_empty(S),!,
    sunify(R,{},C),
    append(C,R1,R3),
    sat_step(R3,R2,_,F).

sat_inv([inv(R,S)|R1],R2,c,F) :-                   % inv(cp(...),S) or inv(cp(...),{...}) or inv(cp(...),cp(...))
    nonvar(R), R = cp(A,B),!,
    sat_step([S = cp(B,A) |R1],R2,_,F).
sat_inv([inv(R,S)|R1],R2,c,F) :-                   % inv(R,cp(...)) or inv({...},cp(...))
    nonvar(S), S = cp(A,B),!,
    sat_step([R = cp(B,A) |R1],R2,_,F).

sat_inv([inv(R,S)|R1],R2,c,F) :-                   % inv({.../R},R) or inv(R,{.../R}) or inv({.../R},{.../R})
    tail(R,TR),                               % [rule inv_3, inv_4, inv_5]
    tail(S,TS),samevar(TR,TS),!,
    sat_inv_same_tail([inv(R,S)|R1],R2,c,F,TS).
sat_inv([inv(R,S)|R1],R2,c,F) :-                   % inv({...},S) or inv({...},{...}) [rule inv_7]
    nonvar(R), R = _ with [X,Y], !,
    sunify(R,RR with [X,Y],C1), append(C1,R1,C1R1),
    sunify(S,SR with [Y,X],C2), append(C1R1,C2,R3),
    sat_step([[X,Y] nin RR,[Y,X] nin SR,inv(RR,SR),rel(RR),rel(SR)|R3],R2,_,F).
sat_inv([inv(R,S)|R1],R2,c,F) :-                   % inv(R,{...}), var R [rule inv_6]
    var(R),
    nonvar(S), S = _ with [X,Y], !,
    sunify(S,SR with [X,Y],C1), append(C1,R1,R3),
%   R = RR with [Y,X],
    sunify(R,RR with [Y,X],_),
    sat_step([[X,Y] nin SR,inv(RR,SR),rel(RR),rel(SR)|R3],R2,_,F).
sat_inv_same_tail([inv(R,S)|R1],R2,c,F,S) :-      % inv({.../R},R), var R [rule inv_3]
    var(S),!,
    R = RR with [X1,Y1],
    replace_tail(RR,N,RRnew),
    S = N with [X1,Y1] with [Y1,X1],
    sat_step([inv(RRnew,N)|R1],R2,_,F).
sat_inv_same_tail([inv(R,S)|R1],R2,c,F,R) :-      % inv(R,{.../R}), var R [rule inv_4]
    var(R),!,
    S = SS with [X1,Y1],
    replace_tail(SS,N,SSnew),
    R = N with [X1,Y1] with [Y1,X1],
    sat_step([inv(SSnew,N)|R1],R2,_,F).
sat_inv_same_tail([inv(R,S)|R1],R2,c,F,T) :-      % inv({.../R},{.../R}), var R [rule inv_5]
    S = _ with [_,_],
    R = RR with [X1,Y1],
    replace_tail(S,{},Selems),
    (   sunify(N1 with [Y1,X1],Selems,C),
        append(C,R1,R3),
        sat_step([[Y1,X1] nin N1, %%??
                  un(T,N1,N2),inv(RR,N2)|R3],R2,_,F)
    ;   T = N with [X1,Y1] with [Y1,X1],
        replace_tail(R,{},Relems),
        replace_tail(RR,N,RRnew),
        replace_tail(S,N,SSnew),
        sat_step([[Y1,X1] nin Selems,[X1,Y1] nin Selems,
                  [Y1,X1] nin Relems,inv(RRnew,SSnew)|R1],R2,_,F)
    ;   T = N with [X1,Y1] with [Y1,X1],
        replace_tail(S,N,SSnew),
        replace_tail(RR,{},RRelems),
        sunify(N3 with [Y1,X1],RRelems,C),
        append(C,R1,R3),
        sat_step([[Y1,X1] nin Selems,[X1,Y1] nin Selems,
                  [Y1,X1] nin N3,
                  un(N,N3,N4),inv(N4,SSnew)|R3],R2,_,F)
    ;   sunify(N5 with [X1,Y1],Selems,C),
        append(C,R1,R3),
        T = N with [Y1,X1],
        replace_tail(RR,N,RRnew),
        sat_step([
                  %% [X1,Y1] nin N5, %% ??
                  [Y1,X1] nin Selems,un(N,N5,N6),inv(RRnew,N6)|R3],R2,_,F)
    ).


%%%%%%%%%%%%%%%%%%%%%% range of a binary relation (ran/2)

sat_ran([ran(X,Y)|R1],R2,c,F) :-                   % ran(X,X)
    var(X),var(Y),X==Y,!, X = {},
    sat_step(R1,R2,_,F).
sat_ran([ran(S,D)|R1],[ran(S,D)|R2],Stop,F) :-     % ran(X,Y), var X,Y (irreducible form)
    var(S),var(D),!,
    sat_step(R1,R2,Stop,F).
sat_ran([ran(S,D)|R1],R2,_,F) :-                   % ran(S,D), D = int(A,B) open interval
    %nonvar(D), D = int(M,N), open_intv(D),!,
    nonvar(D), open_intv(D),!,    
    D = int(M,N),                 
    (sat_step([N < M, S = {}|R1],R2,_,F)
    ;
     b_getval(rw_int,RWInt),
     (apply_st(RWInt,D,R) ->
         sat_step([M =< N, ran(S,R)|R1],R2,_,F)
       ;
         append(RWInt,[[D,R]],RWInt_),
         b_setval(rw_int,RWInt_),
         sat_step([M =< N, subset(R,int(M,N)), size(R,K), K is N-M+1, ran(S,R)|R1],R2,_,F)
     )
    ).
sat_ran([ran(S,D)|R1],R2,c,F) :-                   % ran({},r) 
    nonvar(S),is_empty(S),!,
    sunify(D,{},C),
    append(C,R1,R3),
    sat_step(R3,R2,_,F).
sat_ran([ran(S,D)|R1],R2,c,F) :-                   % ran(int(A,B),r) open interval (case B < A, i.e. empty set)
    nonvar(S), open_intv(S),!,    
    S = int(M,N), 
    sunify(D,{},C),
    append(C,R1,R3),               
    sat_step([N < M|R3],R2,_,F).
sat_ran([ran(S,D)|R1],R2,c,F) :-                   % ran(S,{}) 
    nonvar(D), is_empty(D),!,
    sunify(S,{},C),
    append(C,R1,R3),
    sat_step(R3,R2,_,F).
sat_ran([ran(S,D)|R1],R2,R,F) :-                   % ran(cp(...),D) or ran(S,cp(...))
    (   nonvar(S), S = cp(_,_) ->
        true
    ;
        nonvar(D),D = cp(_,_)
    ),
    !,
    sat_ran_cp([ran(S,D)|R1],R2,R,F).
sat_ran([ran(S,D)|R1],[ran(S,D)|R2],Stop,F) :-     % noran_elim: ran(S,r), var S, nonvar r  (irreducible form)
    var(S), noran_elim,!,
    sat_step(R1,R2,Stop,F).
sat_ran([ran(S,D)|R1],R2,c,F) :-                   % noran_elim: ran({...},r), nonvar r
    nonvar(S), S = SR with [_A1,A2], noran_elim,!,
    sunify(D,DR with A2,C),
    append(C,R1,R3),
        (var(SR),nonvar(DR), DR=_ with _,!,
         sat_step([solved(ran(SR,DR),var(SR),[]),rel(SR),set(DR)|R3],R2,_,F)
         ;
         sat_step([ran(SR,DR),rel(SR),set(DR)|R3],R2,_,F)
        ).
sat_ran([ran(S,D)|R1],R2,c,F) :-                   % ran(S,{t}) or ran(S,int(a,a)) a constant, var S
    var(S),
    nonvar(D), singleton(D,A), !,
    sat_step([comp(R,{} with [A,A],R),S = R with [Z,A],[Z,A] nin R,rel(R)|R1],R2,_,F).
sat_ran([ran(S,D)|R1],[ran(S,D)|R2],Stop,nf) :-   % ran(S,r), var S, nonvar r 
    var(S),!,                                     % delayed until final_sat is called 
    sat_step(R1,R2,Stop,nf).                      
sat_ran([ran(S,D)|R1],R2,c,f) :-                  % ran(S,r), var S, nonvar r (final mode only)
    var(S), nonvar(D), first_rest(D,A,_DR,_) ,!,
    sunify(D,DR with A,C),
    append(C,R1,R3),
    sat_step([A nin DR,ran(S1,{} with A),ran(S2,DR),
              delay(un(S1,S2,S),false),rel(S1),rel(S2),set(DR)|R3],R2,_,f).
sat_ran([ran(S,D)|R1],R2,c,F) :-                  % ran({...},r) 
    nonvar(S), S = SR with [_A1,A2], !,
    sunify(D,DR with A2,C),
    append(C,R1,R3),
    sat_step([ran(SR,DR),rel(SR),set(DR)|R3],R2,_,F).

sat_ran_cp([ran(S,D)|R1],R2,c,F) :-
    sat_step([inv(S,SInv),dom(SInv,D)|R1],R2,_,F).


%%%%%%%%%%%%%%%%%%%%%% composition of binary relations (comp/3)

sat_comp([comp(R,_S,T)|R1],R2,c,F) :-     % comp({},s,t) 
    nonvar(R),is_empty(R),!,
    sunify(T,{},C),
    append(C,R1,R3),
    sat_step(R3,R2,_,F).
sat_comp([comp(_R,S,T)|R1],R2,c,F) :-     % comp(r,{},t) 
    nonvar(S),is_empty(S),!,
    sunify(T,{},C),
    append(C,R1,R3),
    sat_step(R3,R2,_,F).

sat_comp([comp(R,S,T)|R1],[comp(R,S,T)|R2],Stop,F) :-  
    (var_st(R),rel_term(S),var_or_empty(T),!     % comp(R,s,T) or comp(r,S,T), r and s not empty set,
    ;                                % irreducible forms
     var_st(S),rel_term(R),var_or_empty(T)
    ),
    !,
    sat_step(R1,R2,Stop,F).

sat_comp([comp(S1,S2,T)|R1],R2,R,F) :-   % comp(r,s,t) and either r or s or t are not-variable CP
    (nonvar(S1), S1 = cp(_,_) ->
        true
    ;
     nonvar(S2), S2 = cp(_,_) ->
        true
    ;
        nonvar(T), T = cp(_,_)
    ),
    !,
    gcp_to_set(S1,SS1), gcp_to_set(S2,SS2), gcp_to_set(T,TT),
    sat_comp_cp([comp(SS1,SS2,TT)|R1],R2,R,F).

sat_comp([comp(R,S,T)|R1],R2,c,F) :-      % comp({[X,Y]/R},{[A,B]/S},{})
    nonvar(R), R = RR with [X,Y],
    nonvar(S), S = SS with [A,B],
    nonvar(T), is_empty(T), !,
    sat_step([A neq Y,
              comp({} with [X,Y],SS,{}),
              comp(RR,{} with [A,B],{}),
              comp(RR,SS,{}) | R1],R2,_,F).
sat_comp([comp(R,S,T)|R1],R2,c,F) :-      % comp({[X,Y]},{[Z,V]},T) - R,S singleton relations
    nonvar(R), R = RR with [X,Y1], nonvar(RR), is_empty(RR),
    nonvar(S), S = SS with [Y2,Z], nonvar(SS), is_empty(SS), !,
    (   sat_step([Y1 = Y2, T = {} with [X,Z]|R1],R2,_,F)
    ;   sat_step([Y1 neq Y2, T = {}|R1],R2,_,F)
    ).
sat_comp([comp(R,S,T)|R1],R2,c,F) :-      % comp({[X,X]},{[X,Z]/S},{[X,Z]/S}) - R singleton relation
    nonvar(R), R = RR with [X,X], nonvar(RR), is_empty(RR),
    nonvar(S), S = SS with [X,Z],
    nonvar(T), T = TT with [X,Z], TT == SS, !,
    sat_step([comp({} with [X,X],SS,SS) |R1],R2,_,F).
sat_comp([comp(R,S,T)|R1],R2,c,F) :-      % comp({[X,Y]/S},{[Y,Y]},{[X,Y]/S}) - S singleton relation
    nonvar(R), R = RR with [X,Y],
    nonvar(S), S = SS with [Y,Y], nonvar(SS), is_empty(SS),
    nonvar(T), T = TT with [X,Y], TT == RR, !,
    sat_step([comp(RR,{} with [Y,Y],RR) |R1],R2,_,F).

sat_comp([comp(R,S,T)|R1],[comp(R,S,T)|R2],Stop,F) :-      % special cases - irreducible when nocomp_elim
    nocomp_elim,
    tail(R,TR),tail(S,TS),tail(T,TT),
    samevar3(TR,TS,TT),!,
    sat_step(R1,R2,Stop,F).

sat_comp([comp(R,S,T)|R1],R2,c,F) :-      % comp(R,S,W), W={[X,Z]/T}, var(R), var(S); comp_fe
    var(R), var(S), nonvar(T), T = _ with _,                   
    b_getval(smode,prover(Strategies)),   % and the solving mode is prover([comp_fe,...])          
    member(comp_fe,Strategies),!,
    sat_step([foreach([X,Y1] in R,[],
                  foreach([Y2,Z] in S,[],Y1 = Y2 implies [X,Z] in T,true),true),
              foreach([X,Z] in T,[],
                  exists([X1,Y1] in R,exists([Y2,Z2] in S, X = X1 & Y1 = Y2 & Z = Z2)),true) |R1],R2,_,F).

sat_comp([comp(R,S,T)|R1],R2,c,F) :-      % comp(R,S,W), W={[X,Z]/T}, R and S either vars or {...}
    nonvar(T), T = _TT with [X,Z], !,
    sunify(T,TT with [X,Z],C),
    append(C,R1,R3),
    sat_step([[X,Z] nin TT,
             un(Rx,Rt,R),un(Sz,St,S),
             Rx = RR with [X,Y], Sz = SS with [Y,Z],
             [X,Y] nin RR, [Y,Z] nin SS,
             comp({} with [X,X],RR,RR),
             comp(SS,{} with [Z,Z],SS),
             comp({} with [X,X],Rt,{}),
             comp(St,{} with [Z,Z],{}),
             comp(Rx,St,N1),
             comp(Rt,S,N2),
             un(N1,N2,TT) | R3],R2,_,F).
sat_comp([comp(R,S,T)|R1],R2,c,F) :-      % comp({...},{...},W), var(W)
    var(T),
    nonvar(R), R = _ with [_,_],
    nonvar(S), S = _ with [_,_],!,
    comp_distribute(R,S,C,{},T),
    append(C,R1,R3),
    sat_step(R3,R2,_,F).

comp_distribute(R,S,C,T0,T) :-
    var(R),!,
    comp_distribute_first(R,S,C,T0,T).
comp_distribute({},_S,[],T,T) :- !.
comp_distribute(R,S,C,T0,T) :-
    R = RR with [X,Y1],
    comp_distribute_first([X,Y1],S,C1,T0,T1),
    comp_distribute(RR,S,C2,T1,T),
    append(C1,C2,C).

comp_distribute_first(P,S,C,T0,T2) :-
    nonvar(P),P = [_,_],var(S),!,
    C = [comp({} with P,S,T1),un(T0,T1,T2)].
comp_distribute_first(_P,{},[],T,T) :- !.
comp_distribute_first(P1,S,C,T0,T) :-
    var(P1),!,
    C = [comp(P1,S,T1),un(T0,T1,T)].
comp_distribute_first(P1,S,C,T0,T) :-
    S = SR with [Y2,Z],
    C = [comp({} with P1,{} with [Y2,Z],T1),un(T0,T1,T2) | CR],
    comp_distribute_first(P1,SR,CR,T2,T).

sat_comp_cp([comp(X,Y,Z)|R1],R2,c,F) :-            % special cases
    special_cp3(X,Y,Z,TZ,A,B),!,
    %write('special_comp'),nl,
    (TZ={} ; A={} ; B={}),
    sat_step([comp(X,Y,Z)|R1],R2,_,F).
sat_comp_cp([comp(X,Y,Z)|R1],R2,c,F) :-            % comp(X,Y,Z) (not_cp(X), not_cp(Y), not_cp(Z))
    not_cp(X), not_cp(Y), not_cp(Z),!,
    sat_comp([comp(X,Y,Z)|R1],R2,_,F).
sat_comp_cp([comp(X,Y,Z)|R1],R2,c,F) :-            % comp(cp(A,B),cp(C,D),Z)
    nonvar(X), X = cp(A,B), nonvar(Y), Y = cp(C,D),!,
    (   sat_step([inters(B,C,N1), N1 = {}, Z = {}|R1],R2,_,F)
    ;   sat_step([inters(B,C,N1), N1 neq {}, Z = cp(A,D), set(N1)|R1],R2,_,F)
    ).
sat_comp_cp([comp(X,Y,Z)|R1],R2,c,F) :-            % comp(cp(A,B),Y,Z)
    nonvar(X), X = cp(A,B),!,
    sat_step([dres(B,Y,N1), ran(N1,N2), Z = cp(A,N2), rel(N1),set(N2)|R1],R2,_,F).
sat_comp_cp([comp(X,Y,Z)|R1],R2,c,F) :-            % comp(X,cp(A,B),Z)
    nonvar(Y), Y = cp(A,B),!,
    sat_step([rres(X,A,N1), dom(N1,N2), Z = cp(N2,B), rel(N1),set(N2)|R1],R2,_,F).
sat_comp_cp([comp(X,Y,Z)|R1],R2,c,F) :-            % comp(X,Y,cp(A,B)) (not_cp(X), not_cp(Y))
    not_cp(X),not_cp(Y),
    nonvar(Z), Z = cp(_,_),!,
%   cp_to_set(3,Z,Zt,Zu),
%   append(Zu,R1,R3),
%   sat_step([comp(X,Y,Zt),set(Zt)|R3],R2,_,F).
    sat_step([comp(X,Y,T),rel(T),T=Z|R1],R2,_,F).


%%%%%%%%%%%%%%%%%%%%%% domain of partial function (dompf/2)

sat_dompf([dompf(X,Y)|R1],R2,c,F) :-                   % dom(X,X)
    var(X),var(Y),X==Y,!, X = {},
    sat_step(R1,R2,_,F).
sat_dompf([dompf(S,D)|R1],[dompf(S,D)|R2],Stop,F) :-   % dom(S,D), var(S), var(D) (irreducible form)
    var_ris_st(S),var(D),!,
    sat_step(R1,R2,Stop,F).
sat_dompf([dompf(S,D)|R1],R2,c,F) :-                   % dom({},d)
    nonvar(S),is_empty(S),!,
    sunify(D,{},C),
    append(C,R1,R3),
    sat_step(R3,R2,_,F).
sat_dompf([dompf(S,D)|R1],R2,c,F) :-                   % dom(s,{})
    nonvar(D),is_empty(D),!,
    sunify(S,{},C),
    append(C,R1,R3),
    sat_step(R3,R2,_,F).
sat_dompf([dompf(S,D)|R1],R2,c,F) :-                   % dom({[...],...},D) or dom({[...],...},{...}) or dom({[...],...},int(t1,t2))
    nonvar(S), S = SR with [A1,_A2], !,
    sunify(D,DR with A1,C),
    append(C,R1,R3),
    sat_step([dompf(SR,DR)|R3],R2,_,F).
sat_dompf([dompf(S,D)|R1],R2,c,F) :-                   % dom(ris(_ in {_/_},...),D) or dom(ris(_ in {_/_},...),{...}) or dom(ris(_ in {_/_},...),int(t1,t2))
    ris_term(S),!,
    sunify(S,SR with [A1,_A2],C1),
    sunify(D,DR with A1,C2),
    append(C1,R1,C3),append(C3,C2,R3),
    sat_step([dompf(SR,DR)|R3],R2,_,F).
sat_dompf([dompf(S,D)|R1],R2,c,F) :-                   % dom(S,int(a,a)), var(S)
    var(S), closed_intv(D,A,B), A==B,!,
    S = {} with [A,_],
    sat_step(R1,R2,_,F).
sat_dompf([dompf(S,D)|R1],R2,c,F) :-                   % dom(S,int(a,b)), var(S)
    var(S), closed_intv(D,A,B), A<B,!,
    S = SR with [A,_],
    A1 is A + 1,
    sat_step([dompf(SR,int(A1,B))|R1],R2,_,F).
sat_dompf([dompf(S,D)|R1],R2,R,F) :-                   % dom(cp(...),D) or dom(S,cp(...))
    (   nonvar(S), S = cp(_,_) ->
        true
    ;
        nonvar(D), D = cp(_,_)
    ),
    !,
    sat_dom_cp([dom(S,D)|R1],R2,R,F).
sat_dompf([dompf(S,D)|R1],R2,c,F) :-                   % dom(S,{...}) or dom(S,int(A,B)), var(S)
    var(S), nonvar(D),
    sunify(D,DR with A1,C),!,
    sunify(S,SR with [A1,_A2],_),
    append(C,R1,R3),
    sat_step([dompf(SR,DR)|R3],R2,_,F).

%%%%%%%%%%%%%%%%%%%%%% composition of partial functions (comppf/3)

                                         % comppf({},s,t) 
sat_comppf([comppf(R,S,T)|R1],R2,c,F) :-
    nonvar(R),is_empty(R),!,
    sunify(T,{},C),
    append(C,R1,R3),
    sat_step([pfun(S)|R3],R2,_,F).
                                         % comppf(r,{},t) 
sat_comppf([comppf(R,S,T)|R1],R2,c,F) :-
    nonvar(S),is_empty(S),!,
    sunify(T,{},C),
    append(C,R1,R3),
    sat_step([pfun(R)|R3],R2,_,F).
                                         % comppf(R,s,T) or comppf(r,S,T), r and s not empty set,
                                         % irreducible forms
sat_comppf([comppf(R,S,T)|R1],[comppf(R,S,T)|R2],Stop,F) :-
    (   var_ris_st(R),var_or_empty(T) -> % comppf(R,S,T), var(R) or var(S) (irreducible form)
        true
    ;
        var_ris_st(S),var_or_empty(T)
    ),
    !,
    sat_step(R1,R2,Stop,F).
                                         % comppf({[X,Y]},{[A,B]/S},{}) 
sat_comppf([comppf(R,S,T)|R1],R2,c,F) :-
    nonvar(R), R = RR with [_,Y], nonvar(RR), is_empty(RR),
    nonvar(S), S = SS with [A,_],
    nonvar(T),is_empty(T), !,
    sat_step([A neq Y, comppf(R,SS,{}) | R1],R2,_,F).
                                         % comppf({[X,Y]/R},{[A,B]/S},{})
sat_comppf([comppf(R,S,T)|R1],R2,c,F) :-
    nonvar(R), R = RR with [X,Y],
    nonvar(S), S = SS with [A,B],
    nonvar(T),is_empty(T), !,
    sat_step([A neq Y,
              comppf({} with [X,X],RR,{}),   
              comppf({} with [A,A],SS,{}),   
              comppf({} with [X,Y],SS,{}),
              comppf(RR,{} with [A,B],{}),
              comppf(RR,SS,{}) | R1],R2,_,F).
                                         % comppf({[X,Y]},{[Z,V]},T)
sat_comppf([comppf(R,S,T)|R1],R2,c,F) :-
    nonvar(R), R = RR with [X,Y1], nonvar(RR), is_empty(RR),
    nonvar(S), S = SS with [Y2,Z], nonvar(SS), is_empty(SS), !,
    (   sat_step([Y1 = Y2, T = {} with [X,Z] | R1],R2,_,F)
    ;   sat_step([Y1 neq Y2, T = {} |R1],R2,_,F)
    ).
                                         % comppf({[X,Y]/R},{[Y,Z]/S},{[X,Z]/T})
sat_comppf([comppf(R,S,T)|R1],R2,c,F) :-
    nonvar(T), T = TT with [X,Z], !,
    sat_step([R = RR with [X,Y], S = SS with [Y,Z],
              [X,Y] nin RR, [Y,Z] nin SS,
              comppf({} with [X,X],RR,{}),   
              comppf({} with [Y,Y],SS,{}),   
              comppf(RR,{} with [Y,Z],N1),comppf(RR,SS,N2),
              un(N1,N2,TT) | R1],R2,_,F).
                                         % comppf({[X,Y],...},{...},T), T var.
sat_comppf([comppf(R,S,T)|R1],R2,c,F) :-
    var(T),
    nonvar(R), R = RR with [X,Y],!,
    (   sunify(S,SS with [Y,Z],C2),      % Y in dom S
        append(C2,R1,R3),
        sat_step([[Y,Z] nin SS,
                 comppf({} with [X,X],RR,{}),   
                 comppf({} with [Y,Y],SS,{}),   
                 comppf(RR,{} with [Y,Z],N1),
                 comppf(RR,SS,N2),
                 un(N1,N2,TT),
                 T = TT with [X,Z] | R3],R2,_,F)
    ;
        sat_step([comppf({} with [Y,Y],S,{}),  % Y nin dom S
        comppf({} with [X,X],RR,{}), comppf(RR,S,T) | R1],R2,_,F)
    ).


%%%%%%%%%%%%%%%%%%%%%% identity for partial functions (id/2)

sat_id([id(A,S)|R1],R2,c,F) :-                  % id(X,X), var X
    var(A),var(S), samevar(A,S),!,
    A = {},
    sat_step(R1,R2,_,F).
sat_id([id(A,S)|R1],[id(A,S)|R2],Stop,F) :-     % id(X,Y), var X,Y (irreducible form)
    var(A),var(S),!,
    sat_step(R1,R2,Stop,F).
sat_id([id(A,S)|R1],R2,c,F) :-                  % id({},S)
    nonvar(A),is_empty(A),!,
    sunify(S,{},C),
    append(C,R1,R3),
    sat_step(R3,R2,_,F).
sat_id([id(A,S)|R1],R2,c,F) :-                  % id(R,{}) 
    nonvar(S),is_empty(S),!,
    sunify(A,{},C),
    append(C,R1,R3),
    sat_step(R3,R2,_,F).
sat_id([id(A,S)|R1],R2,c,F) :-                   % id(R,int(A,B)) open interval (case B < A, i.e. empty set)
    nonvar(S), open_intv(S),!,    
    S = int(M,N), 
    sunify(A,{},C),
    append(C,R1,R3),               
    sat_step([N < M|R3],R2,_,F).
sat_id([id(A,R)|R1],R2,_,F) :-                   % id(A,R), A = int(M,N) open interval
    nonvar(A), open_intv(A),!,       
    A = int(M,N),                    
    (sat_step([N < M, R = {}|R1],R2,_,F)
    ;
     b_getval(rw_int,RWInt),
     (apply_st(RWInt,A,T) ->
         sat_step([M =< N, id(T,R)|R1],R2,_,F)
       ;
         append(RWInt,[[A,T]],RWInt_),
         b_setval(rw_int,RWInt_),
         sat_step([M =< N, subset(T,int(M,N)), size(T,K), K is N-M+1, id(T,R)|R1],R2,_,F)
     )
    ).
sat_id([id(A,S)|R1],R2,c,F) :-                  % id(int(a,b),S), a and b constants
    nonvar(A), closed_intv(A,X,Y),!,
    sunify(S,SR with [X,X],C1), append(C1,R1,R3),
    X1 is X+1,
    sat_step([[X,X] nin SR,id(int(X1,Y),SR),rel(SR)|R3],R2,_,F).
sat_id([id(A,S)|R1],R2,R,F) :-                  % id(cp(...),S) or id(S,cp(...))
    (   nonvar(A), A = cp(_,_) ->
        true
    ;
        nonvar(S), S = cp(_,_)
    ),
    !,
    sat_id_cp([id(A,S)|R1],R2,R,F).
sat_id([id(A,S)|_R1],_R2,c,_F) :-               % id({.../R},R), var R (special case)
    nonvar(A), var(S),
    tail(A,TA), samevar(TA,S),!,
    fail.
sat_id([id(A,S)|_R1],_R2,c,_F) :-               % id(R,{.../R}), var R (special case)
    nonvar(S), var(A),
    tail(S,TS), samevar(TS,A),!,
    fail.
sat_id([id(A,S)|R1],R2,c,F) :-                  % id({.../R},{.../R}), var R (special case)
    nonvar(A),  tail(A,TA), var(TA),
    nonvar(S),  tail(S,TS), var(TS),
    samevar(TA,TS),!,
    TA = {},
    sat_step([id(A,S)|R1],R2,_,F).
sat_id([id(A,S)|R1],R2,c,F) :-                  % id({...},S) 
    nonvar(A), A = _ with X, !,
    sunify(A,AR with X,C1), append(C1,R1,C1R1),
    sunify(S,SR with [X,X],C2), append(C1R1,C2,R3),
    sat_step([X nin AR,[X,X] nin SR,id(AR,SR),set(AR),rel(SR)|R3],R2,_,F).
sat_id([id(A,S)|R1],R2,c,F) :-                     % id(A,{...}), var A
%   var(A), nonvar(S), S = _ with [X,X], !,
    var(A), nonvar(S), S = _ with [X,Y], sunify(X,Y,_),!,
    sunify(S,SR with [X,Y],C1), append(C1,R1,R3),
    sunify(A,AR with X,C2), append(C2,R3,R4),
    sat_step([X nin AR,[X,Y] nin SR,id(AR,SR),set(AR),rel(SR)|R4],R2,_,F).

sat_id_cp([id(A,S)|R1],[id(A,S)|R2],Stop,F) :-    % id(A,S) (irreducible form)
    var_st(A), var_st(S),!,
    %write('irreducible form CP'),nl,
    sat_step(R1,R2,Stop,F).

sat_id_cp([id(A,S)|R1],R2,c,F) :-                 % id(cp(A,B),A)  or id(cp(B,A),A)  (special cases)
    nonvar(A), A = cp(_,_),
    tail_cp(S,TS),
    tail_cp(A,TA), samevar(TA,TS),!,
    %write(sat_un_cp_special),nl,
    TS = {},
    sat_step([id(A,S)|R1],R2,_,F).

sat_id_cp([id(A,S)|R1],R2,c,F) :-                 % id(cp(...),{...})
%   nonvar(S), S = _ with [X,X], !,
    nonvar(S), S = _ with [X,Y], sunify(X,Y,_),!,
    %write('id(cp(...),{...})'),nl,
    sunify(S,SR with [X,Y],C1), append(C1,R1,R3),
    sunify(A,AR with X,C2), append(C2,R3,R4),
    sat_step([X nin AR,[X,Y] nin SR,id(AR,SR),set(AR),rel(SR)|R4],R2,_,F).

sat_id_cp([id(A,S)|R1],R2,c,F) :-                  % id(cp(...),S), var(S)
    var(S),!,
    nonvar(A), A = cp(S1,S2),
    S1 = Xr with X, S2 = Yr with Y,
    %write('id(cp(...),S)'),nl,
    sunify(S,N1 with [[X,Y],[X,Y]],C), append(C,R1,R3),
    sat_step([id(N2,N1),
              [[X,Y],[X,Y]] nin N1,
              delay(un(cp({} with X,Yr),cp(Xr,Yr with Y),N2),false),
              rel(N1),set(N2) |R3],R2,_,F).

sat_id_cp([id(A,S)|R1],R2,c,F) :-                  % id(a,cp(...))
    nonvar(S), S = cp(Xr,Yr),!,
    %write('id(s,cp(...))'),nl,
    (   sat_step([A={}, Xr={} | R1],R2,_,F)
    ;   sat_step([A={}, Yr={} | R1],R2,_,F)
    ;   sat_step([A={} with _N, Xr=A, Yr=A | R1],R2,_,F)
    ).


%%%%%%%%%%%%
%%%%%% Rewriting rules for defined constraints over binary relations and partial functions %%%%%%
%%%%%%%%%%%%

%%%%%%%%%%%%%%%%%%%%%% range of a binary relation (ran/2)

%sat_ran([ran(R,A)|R1],R2,c,F) :-    % replaced by ad-hoc rules (see above) for efficiency reasons
%        sat_step([inv(R,S),dom(S,A)|R1],R2,_,F).

%%%%%%%%%%%%%%%%%%%%%% domain restriction (dres/3)

sat_dres([dres(A,R,S)|R1],R2,Stop,nf) :-          % dres(A,R,S), A,R,S variables: delayed
    var(A), var(R), var(S), !,
    sat_step([delay(dres(A,R,S),prolog_call(novar3(A,R,S))) | R1],R2,Stop,nf).
sat_dres([dres(A,R,S)|R1],R2,c,F) :-              % dres(A,R,S)
        sat_step([un(S,T,R),rel(T),dom(S,B),set(B),subset(B,A),dom(T,C),set(C),disj(A,C)
        |R1],R2,_,F).

sat_drespf([drespf(A,R,S)|R1],R2,c,F) :-          % drespf(A,R,S) -  only for partial functions
    sat_step([dom(R,DR),set(DR),inters(A,DR,I),subset(S,R),dom(S,I)|R1],R2,_,F).

novar3(A,_R,_S) :- nonvar(A),!.
novar3(_A,R,_S) :- nonvar(R),!.
novar3(_A,_R,S) :- nonvar(S).

%%%%%%%%%%%%%%%%%%%%%% range restriction (rres/3)

sat_rres([rres(R,A,S)|R1],R2,Stop,nf) :-          % rres(R,A,S), A,R,S variables: delayed
    var(A), var(R), var(S), !,
    sat_step([delay(rres(R,A,S),prolog_call(novar3(A,R,S))) | R1],R2,Stop,nf).
sat_rres([rres(R,A,S)|R1],R2,c,F) :-              % rres(R,A,S)
    sat_step([un(S,T,R),rel(T),ran(S,B),set(B),subset(B,A),ran(T,C),set(C),disj(A,C)
    |R1],R2,_,F).

%%%%%%%%%%%%%%%%%%%%%% domain anti-restriction (dares/3)

sat_dares([dares(A,R,S)|R1],R2,Stop,nf) :-       % dares(A,R,S), A,R,S variables: delayed
    var(A), var(R), var(S), !,
    sat_step([delay(dares(A,R,S),prolog_call(novar3(A,R,S))) | R1],R2,Stop,nf).
sat_dares([dares(A,R,S)|R1],R2,c,F) :-           % dares(A,R,S)
    sat_step([un(S,T,R),rel(T),dom(S,B),set(B),dom(T,C),set(C),subset(C,A),disj(A,B)
    |R1],R2,_,F).

%%%%%%%%%%%%%%%%%%%%%% range anti-restriction (rares/3)

sat_rares([rares(R,A,S)|R1],R2,Stop,nf) :-        % rares(R,A,S), A,R,S variables: delayed
    var(A), var(R), var(S), !,
    sat_step([delay(rares(R,A,S),prolog_call(novar3(A,R,S))) | R1],R2,Stop,nf).
sat_rares([rares(R,A,S)|R1],R2,c,F) :-            % rares(R,A,S)
    sat_step([un(S,T,R),rel(T),ran(S,B),set(B),ran(T,C),set(C),subset(C,A),disj(A,B)
        |R1],R2,_,F).

%%%%%%%%%%%%%%%%%%%%%% partial function application (apply/3)

sat_apply([apply(S,X,Y)|R1],R2,c,F) :-            % apply(F,X,Y)
    sat_step([[X,Y] in S,delay(pfun(S),false)|R1],R2,_,F).     

%%%%%%%%%%%%%%%%%%%%%% overriding (oplus/3)

sat_oplus([oplus(R,S,T)|R1],R2,c,F) :-            % oplus(R,S,T)
    sat_step([dom(S,N1),dares(N1,R,N2),un(N2,S,T),set(N1),rel(N2)|R1],R2,_,F).

%%%%%%%%%%%%
%%%%%% Rewriting rules for NEGATIVE constraints over binary relations and partial functions %%%%%%
%%%%%%%%%%%%

%%%%%%%%%%%%%%%%%%%%%% not binary relation (nrel/1)

sat_nrel([nrel(X)|R1],R2,c,F) :-                  % nrel(X)
    sat_step([N in X, npair(N) |R1],R2,_,F).   

%%%%%%%%%%%%%%%%%%%%%% not partial function (npfun/1)

sat_npfun([npfun(X)|R1],R2,c,F) :-                % npfun(X)
    (   sat_step([[N1,N2] in X, [N1,N3] in X, N2 neq N3 |R1],R2,_,F)   
    ;
        nb_getval(type_check,off),
        sat_step([nrel(X) |R1],R2,_,F)  
    ).

%%%%%%%%%%%%%%%%%%%%%% not pair (npair/1)

sat_npair([npair(X)|R1],[npair(X)|R2],Stop,F) :-  % npair(X), var(X), (irreducible form)
    var(X),!,
    sat_step(R1,R2,Stop,F).
sat_npair([npair(X)|R1],R2,c,F) :-                % npair(f(a,b))
    functor(X,Funct,Arity),
    (   Funct \== '[|]' ->
        true
    ;
        Arity \== 2
    ),
    !,
    sat_step(R1,R2,_,F).
sat_npair([npair(X)|R1],R2,c,F) :-                % npair([a])
    X = [_],
    sat_step(R1,R2,_,F).
sat_npair([npair(X)|R1],R2,c,F) :-                % npair([a,b,c,...])
    X = [_A|R], R = [_|S],
    sat_step([S neq []|R1],R2,_,F).

%%%%%%%%%%%%%%%%%%%%%% not domain (ndom/2)

sat_ndom([ndom(R,A)|R1],R2,c,F) :-                % ndom(R,A)
    (   
        sat_step([[N1,_N2] in R, N1 nin A |R1],R2,_,F)
    ;   
        sat_step([N1 in A, comp({} with [N1,N1],R,{}) |R1],R2,_,F)
        %sat_step([N1 in A, dom(R,D), N1 nin D, set(D)|R1],R2,_,F)    %alternative implementation
    ;
        nb_getval(type_check,off),
        sat_step([nrel(R)|R1],R2,_,F)
    ).

%%%%%%%%%%%%%%%%%%%%%% not inverse (ninv/2)

sat_ninv([ninv(R,S)|R1],R2,c,F) :-                % ninv(R,R)
    var(R),var(S),R == S,!,
    (   sat_step([[N1,N2] in R, [N2,N1] nin R|R1],R2,_,F)
        %sat_step([R = N with [N1,N2], [N2,N1] nin N, N1 neq N2|R1],R2,_,F)  %alternative implementation
    ;
        nb_getval(type_check,off),
        sat_step([nrel(R)|R1],R2,_,F)
    ).
sat_ninv([ninv(R,S)|R1],R2,c,F) :-                % ninv(R,S)
    (   
        sat_step([[N1,N2] in R, [N2,N1] nin S|R1],R2,_,F)
    ;   
        sat_step([[N1,N2] nin R, [N2,N1] in S|R1],R2,_,F)
    ;
        nb_getval(type_check,off),
        sat_step([nrel(R)|R1],R2,_,F)
    ;
        nb_getval(type_check,off),
        sat_step([nrel(S)|R1],R2,_,F)
    ).

%%%%%%%%%%%%%%%%%%%%%% not composition (ncomp/3)

sat_ncomp([ncomp(R,S,T)|R1],R2,c,F) :-            % ncomp(R,S,T)
    (   
        sat_step([[X,Y] in R, [Y,Z] in S, [X,Z] nin T|R1],R2,_,F)
    ;   
        sat_step([[X,Z] in T,
        comp({} with [X,X],R,N1),
        comp(S,{} with [Z,Z],N2),
        comp(N1,N2,{}) |R1],R2,_,F)
    ;
        nb_getval(type_check,off),
        sat_step([nrel(R)|R1],R2,_,F)
    ;
        nb_getval(type_check,off),
        sat_step([nrel(S)|R1],R2,_,F)
    ;
        nb_getval(type_check,off),
        sat_step([nrel(T)|R1],R2,_,F)
    ).

%%%%%%%%%%%%%%%%%%%%%% not range (nran/2)

sat_nran([nran(R,A)|R1],R2,c,F) :-                % nran(R,A)
    (   sat_step([[_N1,N2] in R, N2 nin A|R1],R2,_,F)
    ;   sat_step([N1 in A, comp(R,{} with [N1,N1],{})|R1],R2,_,F)
%   ;   sat_step([ran(R,RR), N2 nin RR, N2 in A, set(RR) |R1],R2,_,F)   %alternative implementation
    ;
        nb_getval(type_check,off),
        sat_step([nrel(R)|R1],R2,_,F)
    ).

%%%%%%%%%%%%%%%%%%%%%% not domain restriction (ndres/3)

sat_ndres([ndres(A,R,S)|R1],R2,c,F) :-
    (   sat_step([[N1,_N2] in S,N1 nin A|R1],R2,_,F)
    ;   sat_step([[N1,N2] in S,[N1,N2] nin R|R1],R2,_,F)
    ;   sat_step([[N1,N2] in R,N1 in A,[N1,N2] nin S|R1],R2,_,F)
    ;
        nb_getval(type_check,off),
        sat_step([nrel(R)|R1],R2,_,F)
    ;
        nb_getval(type_check,off),
        sat_step([nrel(S)|R1],R2,_,F)
    ).

%%%%%%%%%%%%%%%%%%%%%% not domain anti-restriction (ndares/3)

sat_ndares([ndares(A,R,S)|R1],R2,c,F) :-
    (   sat_step([[N1,_N2] in S,N1 in A|R1],R2,_,F)
    ;   sat_step([[N1,N2] in S,[N1,N2] nin R|R1],R2,_,F)
    ;   sat_step([[N1,N2] in R,N1 nin A,[N1,N2] nin S|R1],R2,_,F)
    ;
        nb_getval(type_check,off),
        sat_step([nrel(R)|R1],R2,_,F)
    ;
        nb_getval(type_check,off),
        sat_step([nrel(S)|R1],R2,_,F)
    ).

%%%%%%%%%%%%%%%%%%%%%% not range restriction (nrres/3)

sat_nrres([nrres(R,A,S)|R1],R2,c,F) :-
    (   sat_step([[_N1,N2] in S,N2 nin A|R1],R2,_,F)
    ;   sat_step([[N1,N2] in S,[N1,N2] nin R|R1],R2,_,F)
    ;   sat_step([[N1,N2] in R,N2 in A,[N1,N2] nin S|R1],R2,_,F)
    ;
        nb_getval(type_check,off),
        sat_step([nrel(R)|R1],R2,_,F)
    ;
        nb_getval(type_check,off),
        sat_step([nrel(S)|R1],R2,_,F)
    ).

%%%%%%%%%%%%%%%%%%%%%% not range anti-restriction (nrares/3)

sat_nrares([nrares(R,A,S)|R1],R2,c,F) :-
    (   sat_step([[_N1,N2] in S,N2 in A |R1],R2,_,F)
    ;   sat_step([[N1,N2] in S,[N1,N2] nin R |R1],R2,_,F)
    ;   sat_step([[N1,N2] in R,N2 nin A,[N1,N2] nin S |R1],R2,_,F)
    ;
        nb_getval(type_check,off),
        sat_step([nrel(R)|R1],R2,_,F)
    ;
        nb_getval(type_check,off),
        sat_step([nrel(S)|R1],R2,_,F)
    ).

%%%%%%%%%%%%%%%%%%%%%% not relational image (nrimg/3)

sat_nrimg([nrimg(R,A,B)|R1],R2,c,F) :-
    (   sat_step([N0 nin B,dres(A,R,N1),[N3,N0] in N1,N3 in A,rel(N1)|R1],R2,_,F)
    ;   sat_step([N0 in B,dres(A,R,N1),ran(N1,N2),N0 nin N2,rel(N1),set(N2)|R1],R2,_,F)
    ;
        nb_getval(type_check,off),
        sat_step([nrel(R)|R1],R2,_,F)
    ).

%%%%%%%%%%%%%%%%%%%%%% not overriding (noplus/3)

sat_noplus([noplus(R,S,T)|R1],R2,c,F) :-
    (   sat_step([[N1,N2] in T,[N1,N2] nin S,[N1,N2] nin R |R1],R2,_,F)
    ;   sat_step([[N1,N2] nin T, [N1,N2] in S |R1],R2,_,F)
    ;   sat_step([[N2,N3] in T,[N2,N3] nin S,dom(S,N1),N2 in N1,set(N1) |R1],R2,_,F)
    ;   sat_step([[N2,N3] nin T,[N2,N3] in R,dom(S,N1),N2 nin N1,set(N1) |R1],R2,_,F)
    ;
        nb_getval(type_check,off),
        sat_step([nrel(R)|R1],R2,_,F)
    ;
        nb_getval(type_check,off),
        sat_step([nrel(S)|R1],R2,_,F)
    ;
        nb_getval(type_check,off),
        sat_step([nrel(T)|R1],R2,_,F)
    ).

%%%%%%%%%%%%%%%%%%%%%% not identity (nid/2)

sat_nid([nid(A,S)|R1],R2,c,F) :-
    (   sat_step([N1 in A, [N1,N1] nin S |R1],R2,_,F)
    ;   sat_step([N1 neq N2, [N1,N2] in S |R1],R2,_,F)
    ;   sat_step([N1 nin A, [N1,N1] in S |R1],R2,_,F)
    ;
        nb_getval(type_check,off),
        sat_step([P in S, npair(P) |R1],R2,_,F)
    ).

%%%%%%%%%%%%%%%%%%%%%% not function application (napply/3)

sat_napply([napply(S,X,Y)|R1],R2,c,F) :-
    (   
        sat_step([[X,Y] nin S|R1],R2,_,F)
    ;   
        sat_step([delay(npfun(S),false)|R1],R2,_,F)
    ).

%%%%%%%%%%%%%%%%%%%%%% not domain of partial function (ndompf/2)

sat_ndompf([ndompf(S,A)|R1],R2,c,F) :-
    (   
        sat_step([ndom(S,A)|R1],R2,_,F)
    ;   
        %sat_step([npfun(S)|R1],R2,_,F)
        sat_step([[N1,N2] in S, [N1,N3] in S, N2 neq N3 |R1],R2,_,F)
    ).

%%%%%%%%%%%%%%%%%%%%%% foreach - nforeach

/* 
% This should be implemented at the subset level
% but is easier this way. If subset is called with 
% second argument RIS whose domain is a variable
% interval, the interval won't be substituted.
%
% Don't know how to avoid repeating the precondition
% Not sure how to use the "if" in this case
% If I don't repeat the precondition the next rule
% is applied too

sat_foreach4([foreach(D,P,Fo,FP)|R1],R2,c,F) :-           % foreach(X in int(M,N),P,Fo,FP) open interval
    nonvar(D), D = (V in Dom), 
    nonvar(Dom), Dom = int(M,N), open_intv(Dom),!,
    (nonvar(D), D = (V in Dom), Dom = int(M,N), open_intv(Dom) ->
        (sat_step([N < M|R1],R2,_,F)
        ;
         b_getval(rw_int,RWInt),
         (apply_st(RWInt,Dom,R) ->
             sat_step([M =< N, subset(R,ris(V in R,P,Fo,V,FP))|R1],R2,_,F)
           ;
             append(RWInt,[[Dom,R]],RWInt_),
             b_setval(rw_int,RWInt_),
             sat_step([M =< N,
                       subset(R,int(M,N)),
                       size(R,K),
                       K is N-M+1,
                       subset(R,ris(V in R,P,Fo,V,FP))|R1],R2,_,F)
         )
        )
    ;
        msg_sort_error(foreach)    
    ).

sat_foreach4([foreach(D,P,Fo,FP)|R1],R2,c,F) :-         % foreach(C in Dom,P,Fo,FP)    
    (nonvar(D), D = (V in Dom) ->
        sat_step([subset(Dom,ris(V in Dom,P,Fo,V,FP))|R1],R2,_,F)
    ;
        msg_sort_error(foreach)
    ).
*/ 

sat_foreach4([foreach(D,P,Fo,FP)|R1],R2,c,F) :-         % foreach(C in Dom,P,Fo,FP)    
    (nonvar(D), D = (V in Dom) ->
        (nonvar(Dom), open_intv(Dom) ->
            Dom = int(M,N),
            (  sat_step([N < M|R1],R2,_,F)
            ;
               b_getval(rw_int,RWInt),
               (apply_st(RWInt,Dom,R) ->
                  sat_step([M =< N, subset(R,ris(V in R,P,Fo,V,FP))|R1],R2,_,F)
               ;
                  append(RWInt,[[Dom,R]],RWInt_),
                  b_setval(rw_int,RWInt_),
                  sat_step([M =< N,
                       subset(R,int(M,N)),
                       size(R,K),
                       K is N-M+1,
                       subset(R,ris(V in R,P,Fo,V,FP))|R1],R2,_,F)
               )
             )
        ;
            sat_step([subset(Dom,ris(V in Dom,P,Fo,V,FP))|R1],R2,_,F)
        )
    ;
        msg_sort_error(foreach)    
    ).

sat_nforeach4([nforeach(CE_Dom,V,Fl,PP)|R1],R2,c,F) :-  % nforeach(C in Dom,P,Fo,FP)  
    (nonvar(CE_Dom), CE_Dom = (CtrlExpr in Dom) ->
        ctrl_expr(CtrlExpr,V,LV,CtrlExprNew),
        chvar(LV,[],_FVars,[Fl,CtrlExpr,PP,CtrlExpr],[],_FVarsNew,[FlNew,_PNew,PPNew,CtrlExprNew]),
        %%%%%find_corr_list(CtrlExpr,CtrlExprNew,FVars,FVarsNew),
        negate(FlNew,NegFl),
        get_preconditions(PPNew,PosPre,NegPre),
        conj_append(PosPre,PPNew,PreFP),
        conj_append(PreFP,NegFl,PreNegFl),
        mk_atomic_constraint((PreNegFl or NegPre),NegFlD),
        sat_step([CtrlExprNew in Dom,NegFlD|R1],R2,_,F)
    ;  
        msg_sort_error(foreach)    
    ).

sat_foreach2([foreach(V,G)|R1],R2,c,F) :-              % foreach(X,FP), var X  
    (var(V) ->                               
        catch(rewrite_foreach2(foreach(V,G),Constr),setlog_excpt(Msg),excpt_action(Msg)),!, 
        append(Constr,R1,R3),
        sat_step(R3,R2,_,F)
    ;                                        
        msg_sort_error(foreach)  
    ).

rewrite_foreach2(foreach(Y,X neq Y),_) :-                         % foreach(Y,X neq Y)
    var(X), var(Y), !,
    fail.
rewrite_foreach2(foreach(V,G),C) :-                       
    var(V),!,
    rewrite_foreach2(foreach([V],G),C).
rewrite_foreach2(foreach(Vars,foreach(Z,G)),C) :-  !,             % nested foreach - soluzione provvisoria
    rewrite_foreach2(foreach([Z|Vars],G),C).
rewrite_foreach2(foreach(Vars,nexists(Z,G)),C) :-  !,             % nested nexists 
    negate(G,NegG),
    rewrite_foreach2(foreach([Z|Vars],NegG),C).
%rewrite_foreach2(foreach(_Vars,_T1 neq _T2),[]) :- !,                % foreach(Vars,t1 neq t2[Y])
%    print_single_warning('***WARNING***: foreach(Vars,T1 neq T2) not implemented yet').
%rewrite_foreach2(foreach(_Vars,_T1 nin _T2),[]) :- !,                % foreach(Vars,t1 nin t2[Y])
%    print_single_warning('***WARNING***: foreach(Vars,T1 nin T2) not implemented yet').
rewrite_foreach2(foreach(_Vars,_G),_) :- !,                       % unsupported foreach
    throw(setlog_excpt('not supported form of foreach/2')).       
%%%%% TO BE COMPLETED 

sat_nforeach2([nforeach(_,_)|_R1],_R2,c,_F) :-         % nforeach(C,FP)  
    msg_sort_error(foreach).   

%%%%%%%%%%%%%%%%%%%%%% exists - nexists

sat_exists([exists(V,Fo)|R1],R2,c,F) :-               % exists(V,Fo), var(V)  
    var(V),!,
    chvar([V],[],_,Fo,[],_,NewFo),
    mk_atomic_constraint(NewFo,Constr),
    sat_step([Constr|R1],R2,_,F).
sat_exists([exists(CE_Dom,Fo)|R1],R2,c,F) :-          % exists(V in D,Fo) 
    %nonvar(CE_Dom), CE_Dom = (_CtrlExpr in _Dom), !,
    sat_nforeach4([nforeach(CE_Dom,[],neg(Fo),true)|R1],R2,_,F).

sat_nexists([nexists(V,Fo)|R1],R2,c,F) :-             % exists(V,Fo), var(V)  
    var(V),!,
    negate_exists(V,Fo,NewFo,C1),
    mk_atomic_constraint(NewFo,Constr),
    append(C1,R1,R3),
    sat_step([Constr|R3],R2,_,F).
sat_nexists([nexists(CE_Dom,Fo)|R1],R2,c,F) :-        % nexists(V in D,Fo)
    sat_foreach4([foreach(CE_Dom,[],neg(Fo),true)|R1],R2,_,F).   

sat_exists4([exists(CE_Dom,P,Fo,FP)|R1],R2,c,F) :-    % exists(V in D,Fo)
    sat_nforeach4([nforeach(CE_Dom,P,neg(Fo),FP)|R1],R2,_,F).   
sat_nexists4([nexists(CE_Dom,P,Fo,FP)|R1],R2,c,F) :-  % nexists(V in D,Fo)
    sat_foreach4([foreach(CE_Dom,P,neg(Fo),FP)|R1],R2,_,F).   

negate_exists(Y,(B1 & true),NegB,C) :- !,   
    negate_exists(Y,B1,NegB,C).
negate_exists(Y,(B1 & B2),NegB,C) :- !,   
    (\+occurs(Y,B1) ->              %Y does not occur in B1
     negate(B1,NB1),
     negate_exists(Y,B2,NB2,C),
     NegB = (NB1 or NB2)
    ;
     occurs(Y,B2) ->
     naf_negate((B1 & B2),C), 
     NegB = (X=X)
    ;
     negate_exists(Y,B1,NB1,C),     %Y occurs in B1 but not in B2
     negate(B2,NB2),
     NegB = (NB1 or NB2)
    ).
negate_exists(Y,(B1 or B2),(NB1 & NB2),C) :- !,   %N.B. the existential quantifier distributes over disjuction
    negate_exists(Y,B1,NB1,C1),                    %(but not conjunction)
    negate_exists(Y,B2,NB2,C2),
    append(C1,C2,C).
negate_exists(Y,A,NegA,C) :-      
    (\+occurs(Y,A) -> 
     negate(A,NegA), 
     C=[]
    ; 
     negate(A,B),
     catch(rewrite_foreach2(foreach(Y,B),C),_Msg,naf_negate(A,C)),
     NegA = (X=X)
    ). 

%%%%%%%%%%%%%%%%%%%%%% let - nlet

sat_let([let(LVars,Conj,Frm)|R1],R2,c,F) :-               
    chvar(LVars,[],_,[Conj,Frm],[],_LVarsNew,[Conj1,Frm1]), 
    mk_atomic_constraint(Conj1,ConjD),
    mk_atomic_constraint(Frm1,FrmD),
    sat_step([ConjD,FrmD|R1],R2,_,F). 

sat_nlet([nlet(LVars,Conj,Frm)|R1],R2,c,F) :-               
    chvar(LVars,[],_,[Conj,Frm],[],_LVarsNew,[Conj1,Frm1]), 
    negate(Frm1,NegFrm),
    mk_atomic_constraint(Conj1,ConjD),
    mk_atomic_constraint(NegFrm,NegFrmD),
    sat_step([ConjD,NegFrmD|R1],R2,_,F).


%%%%%%%%%%%%
%%%%%%%%%%%% Rewriting rules for control constraints %%%%%%%%%%%%
%%%%%%%%%%%%

%%%%%%%%%%%%%%%%%%%%%%% delay mechanism

sat_delay([delay(A,_G)|R1],R2,c,f) :-
    final,!,
    solve_goal_f(A,C2),
    append(C2,R1,R3),
    sat_step(R3,R2,_,f).
sat_delay([delay(A,G)|R1],R2,c,F) :-
    solve_goal_nf(G,C1),!,
    solve_goal_nf(A,C2),
    append(C1,C2,C3),
    append(C3,R1,R3),
    sat_step(R3,R2,_,F).
sat_delay([X|R1],[X|R2],Stop,F) :-
    sat_step(R1,R2,Stop,F).

%%%% solve_goal_f(+Goal,-Constraint)        % Goal: {log} goal in internal form
%                                           % Same as solve_goal_nf/2 but calling
solve_goal_f(G,ClistNew) :-                 % solve_goal_constr_f instead of solve_goal_constr_nf
    constrlist(G,GClist,GAlist),            % (used in sat_delay/4)
    solve_goal_constr_f(GClist,GAlist,ClistNew).

solve_goal_constr_f(Clist,[],CListCan) :- !,
    sat(Clist,CListCan,f).
solve_goal_constr_f(Clist,[true],CListCan) :- !,
    sat(Clist,CListCan,f).
solve_goal_constr_f(Clist,[A|B],CListOut) :-
    sat(Clist,ClistSolved,f),
    sat_or_solve(A,ClistSolved,ClistNew,AlistCl,f),
    append(AlistCl,B,AlistNew),
    solve_goal_constr_f(ClistNew,AlistNew,CListOut).

%%%%%%%%%%%%%%%%%%%%%%% solved mechanism

sat_solved([solved(C,G,Lev)|R1],[solved(C,G,Lev)|R2],Stop,F) :-
    call(G),!,                % if G is true --> mantain C solved; CS is unchanged
    sat_step(R1,R2,Stop,F).
sat_solved([solved(C,_,_)|R1],R2,c,F) :-
    sat_step([C|R1],R2,_,F).  % if G is false --> remove solved; add C to CS


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%      Level 2     %%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%  Check pairs of constraints   %%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%replace-rule:
% C1 &...& Ck &... --X-> C1_1 &...& C1_n &...& Ck &... (k >= 2)
% e.g.:
% dom(S,N) &...& dom(S,M) &... --X-> N=M &...& dom(S,M) &...

%inference-rule:
% C1 &...& Ck & ... --+->
%     solved(C1,...) & D1 &...& Dn &...& Ck &... (k >= 2)
% e.g.:
% dom(S,D) &...& D neq {}  &... -+->
%     solved(dom(S,D),(var(S),var(D)),[1|L]) & S neq {} &...& D neq {} &...

%fail-rule:
% C1 &...& Ck &... ---> fail
% e.g.:
% set(S) &...& nset(S) &... ---> fail

%%%%%%%%%%%%%%%%%%%%%%%%%% global_check1 %%%%%%%%%%%%%%%%%%%%%%%%%
% check type clashes, apply neq elimination, force set cardinality
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

global_check1([],_,[],_) :- !.
global_check1([glb_state(Rel)|RC],GC,[glb_state(Rel)|NewC],F) :- !,
    global_check1(RC,GC,NewC,F).         % glb_state: nothing to do

%%%%%% type clashes

global_check1([C|RC],GC,[C|NewC],F) :-   % type clashes --> fail
    type_constr(C),!,
    no_type_error_all(C,RC),
    global_check1(RC,GC,NewC,F).

%%%%%% neq elimination: X neq t, X set variable (only in final mode)

global_check1([C|RC],GC,NewC,f) :-       % neq: W neq T and W or T set variables
    \+ noneq_elim,                       % W neq T & ... & Ck[W,T] & ... --X->
    is_neq(C,1,W,T),                     %        ((Z in W & Z nin T) or (Z nin W & Z in T)) & ... & Ck[W,T]  & ...
    var(W), var(T),                      % Ck either un/3 or subset/2 or inters/3 or diff/3 or size/2 or
    find_setconstraint(W,T,GC,X,Y),!,    % dom/2 or ran/2 or comp/3 or inv/2 or id/2 or ris = {} or ris = ris
    trace_irules('setvar-neq_var'),
    mk_new_constr(X,Y,OutC),
    append(OutC,CC,NewC),
    global_check1(RC,GC,CC,f).
global_check1([C|RC],GC,NewC,f) :-       % neq: W neq {...} and W a set variable
    \+ noneq_elim,                       % W neq {} & ... & Ck[W] & ... --X->   Z in W & ... & Ck[W]  & ...
    is_neq(C,1,W,T),                     % W neq {...} & ... & Ck[W] & ... --X->
    var(W), aggr_term(T),                %        ((Z in W & Z nin {...}) or (Z nin W & Z in {...})) & ... & Ck[W]  & ...
    find_setconstraint(W,GC),!,
    trace_irules('setvar-neq_set'),
    mk_new_constr2(W,T,OutC),
    append(OutC,CC,NewC),
    global_check1(RC,GC,CC,f).

%%%%%% force set cardinality

global_check1([C|RC],GC,Res,f) :-
   \+size_solver_on,                % (size_solver_on = false) size(S,N), var S, var N
    is_size(C,_,S,N),var(S),var(N),!,
    GC = cs(ICS,_),
    %DBG write('constraint: '),write(ICS),nl,
    minimize(ICS,N,M),
    %DBG write('min.: '),write(M),nl,
    (M == 0 ->
          Res=[solved(size(S,N),(var(S),var(N)),2)|NewC]
     ;
          mk_set_atleastN_var(M,R,S,C1),
          solve_int(K is N-M,R2),
          append(C1,R2,R3),
          append([size(R,K)|R3],NewC,Res)
    ),
    global_check1(RC,GC,NewC,f).

%%%%%% all other cases

global_check1([C|RC],GC,[C|NewC],F) :-!,  % all other constraints - nothing to do
    global_check1(RC,GC,NewC,F).


%%%%%%%%%%%%%%%%%%%%%%%%%% global_check2 %%%%%%%%%%%%%%%%%%%%%%%%%
% inference rules:
% unicity property, size inference, dom-ran-comp inference rules
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

global_check2([],_,[],_) :- !.
global_check2([glb_state(Rel)|RC],GC,[glb_state(Rel)|NewC],F) :- !,  % glb_state: nothing to do
    global_check2(RC,GC,NewC,F).
global_check2([X neq Y|RC],GC,[X neq Y|NewC],F) :- !,                % neq: nothing to do
    global_check2(RC,GC,NewC,F).
global_check2([C|RC],GC,[C|NewC],F) :-                               % type_constr: nothing to do
    type_constr(C),!,
    global_check2(RC,GC,NewC,F).
global_check2([solved(C,Cond,Lvl)|RC],GC,NewC,F) :- !,               % temporaly remove 'solved' mode
    global_check2(C,[solved(C,Cond,Lvl)|RC],GC,NewC,F).
global_check2([C|RC],GC,NewC,F) :-                                   % process all other constraints
    global_check2(C,[C|RC],GC,NewC,F).

%%%%%%%%%%%%%%%%%%%%%%% compulsory rules %%%%%%%%%%%%%%%%%%%%%%%%%

%%%%%% unicity property

global_check2(size(_,_),[C|RC],GC,NewC,F) :-      % size-size: size(S,N) & size(S,M) ---> size(S,M) & N=M
    is_size(C,1,X,N),
    var(X),
    find_size(X,RC,M),!,
    %trace_irules('size-size'),
    N = M,
    global_check2(RC,GC,NewC,F).

global_check2(un(_,_,_),[C|RC],GC,NewC,F) :-      % un-un: un(X,Y,Z1) & un(X,Y,Z2) or un(X,Y,Z1) & un(Y,X,Z2)
    is_un_l(C,_,X,Y,Z1),                          % --X-> un(X,Y,Z1) & Z1 = Z2
    var(X),var(Y),var(Z1),
    find_un2(X,Y,RC,Z2), !,
    %trace_irules('un-un'),
    sunify(Z1,Z2,CEq),
    append(CEq,NewC1,NewC),
    global_check2(RC,GC,NewC1,F).

global_check2(diff(_,_,_),[C|RC],GC,NewC,F) :-    % diff-diff: diff(X,Y,Z1) & diff(X,Y,Z2)
    is_diff(C,_,X,Y,Z1),                          % --X-> diff(X,Y,Z1) & Z1 = Z2
    var(X),var(Y),var(Z1),
    find_diff(X,Y,RC,Z2), !,
    %trace_irules('diff-diff'),
    sunify(Z1,Z2,CEq),
    append(CEq,NewC1,NewC),
    global_check2(RC,GC,NewC1,F).

global_check2(dom(_,_),[C|RC],GC,NewC,F) :-       % dom-dom: dom(X,N) & dom(X,M) --X-> dom(X,M) & N=M
    is_dom_l(C,_,X,N,_),
    var(X),
    find_dom(X,RC,M),!,
    trace_irules('dom-dom'),
    sunify(N,M,CEq),
    append(CEq,NewC1,NewC),
    global_check2(RC,GC,NewC1,F).
global_check2(dompf(_,_),[C|RC],GC,NewC,F) :-     % dompf-dompf: dompf(X,N) & dompf(X,M) --X-> dompf(X,M) & N=M
    is_dom_l(C,_,X,N,_),
    var(X),
    find_dom(X,RC,M),!,
    trace_irules('dom-dom'),
    sunify(N,M,CEq),
    append(CEq,NewC1,NewC),
    global_check2(RC,GC,NewC1,F).
global_check2(ran(_,_),[C|RC],GC,NewC,F) :-       % ran-ran: ran(X,N) & ran(X,M) --X-> ran(X,M) & N=M
    is_ran_l(C,_,X,N),
    var(X),
    find_ran(X,RC,M),!,
    %trace_irules('ran-ran'),
    sunify(N,M,CEq),
    append(CEq,NewC1,NewC),
    global_check2(RC,GC,NewC1,F).

%%%%%% temporaly disabled for efficiency reasons %%%%%%%
/*
global_check2(smin(_,_),[C|RC],GC,NewC,F) :-      % min-min: smin(S,N) & smin(S,M) --X-> smin(S,M) & N=M
    is_min(C,1,X,N),
    var(X),
    find_min(X,RC,M),!,
    %trace_irules('min-min'),
    N = M,
    global_check2(RC,GC,NewC,F).
global_check2(smax(_,_),[C|RC],GC,NewC,F) :-      % max-max: smax(S,N) & smax(S,M) --X-> smax(S,M) & N=M
    is_max(C,1,X,N),
    var(X),
    find_max(X,RC,M),!,
    %trace_irules('max-max'),
    N = M,
    global_check2(RC,GC,NewC,F).
global_check2(sum(_,_),[C|RC],GC,NewC,F) :-       % sum-sum: sum(S,N) & sum(S,M) --X-> sum(S,M) & N=M
    is_sum(C,1,X,N),
    var(X),
    find_sum(X,RC,M),!,
    %trace_irules('sum-sum'),
    N = M,
    global_check2(RC,GC,NewC,F).
*/

%%%%%% all other constraints

global_check2(_,[C|RC],GC,[C|NewC],F) :-           % if noirules, all other constraints - nothing to do
    noirules,!,
    global_check2(RC,GC,NewC,F).

%%%%%%%%%%%%%%%%%%%%%%%%%%%% optional rules %%%%%%%%%%%%%%%%%%%%%%%%%%%%%

global_check2(subset(_,_),[Constr|RC],GC,NewCS,F) :-    % subset(int(A,B),S) & subset(int(A,C),S) --X->  
    is_sub_intv(Constr,_,A,B,S),                        % subset(int(A,M),S), where M = max(B,C)
    find_del_sub_intv1(A,S,RC,C,RCnew),!,  
    trace_irules('subset-intv'),
    (NewCS = [B =< C,subset(int(A,C),S)|NewC]
    ;
     NewCS = [C < B,subset(int(A,B),S)|NewC]
    ),
    global_check2(RCnew,GC,NewC,F).
global_check2(subset(_,_),[Constr|RC],GC,NewCS,F) :-    % subset(int(A,B),S) & subset(int(C,B),S) --X->     
    is_sub_intv(Constr,_,A,B,S),                        % subset(int(m,B),S), where m = min(A,C)
    find_del_sub_intv2(B,S,RC,C,RCnew),!,  
    trace_irules('subset-intv'),
    (NewCS = [A =< C,subset(int(A,B),S)|NewC]
    ;
     NewCS = [C < A,subset(int(C,B),S)|NewC]
    ),
    global_check2(RCnew,GC,NewC,F).

global_check2(dom(_,_),C,GC,AddedC,F) :-           % dom-neq
    global_check2_dom(C,GC,AddedC,F),!.

global_check2(dompf(_,_),C,GC,AddedC,F) :-         % dompf-neq, dompf-size
    global_check2_dompf(C,GC,AddedC,F),!.

global_check2(ran(_,_),C,GC,AddedC,F) :-           % ran-neq, ran-size
    global_check2_ran(C,GC,AddedC,F),!.
                                                   % int-not empty: int(A,B)={} & int(A,B) neq {} (A,B var) --> fail

global_check2(un(_,_,_),C,GC,AddedC,F) :-          % un-rel/pfun, un-size
    global_check2_un(C,GC,AddedC,F),!.

%%%%%% all other constraints

global_check2(_,[C|RC],GC,[C|NewC],F) :-           % all other constraints - nothing to do
    global_check2(RC,GC,NewC,F).

%%%%%%%%%%

global_check2_dom([C|RC],GC,AddedC,F) :-
    is_dom_l(C,L,S,D,RorF),             % dom-neq: dom(S,D) & D neq {} --+-> dom(S,D) & D neq {} & S neq {}
    var(S),var(D),\+member(1,L),
    find_neq(D,GC),
    !,
    %trace_irules('dom-neq_dom'),
    add_dom_neq(RorF,S,D,AddedC,L,NewC),
    global_check2(RC,GC,NewC,F).
global_check2_dom([C|RC],GC,AddedC,F) :-
    is_dom_l(C,L,S,D,RorF),             % dom-neq: dom(S,D) & S neq {} --+-> dom(S,D) & D neq {} & S neq {}
    var(S),var(D),\+member(1,L),
    find_neq(S,GC),
    !,
    %trace_irules('dom-neq_rel'),
    add_dom_neqd(RorF,S,D,AddedC,L,NewC),
    global_check2(RC,GC,NewC,F).

global_check2_dompf([C|RC],GC,AddedC,F) :-
    is_dom_l(C,L,S,D,RorF),             % dompf-neq: dompf(S,D) & D neq {} --+-> dompf(S,D) & D neq {} & S neq {}
    var(S),var(D),\+member(1,L),
    find_neq(D,GC),
    !,
    %trace_irules('dom-neq_dom'),
    add_dom_neq(RorF,S,D,AddedC,L,NewC),
    global_check2(RC,GC,NewC,F).
global_check2_dompf([C|RC],GC,AddedC,F) :-
    is_dom_l(C,L,S,D,RorF),             % dompf-neq: dompf(S,D) & S neq {} --+-> dompf(S,D) & D neq {} & S neq {}
    var(S),var(D),\+member(1,L),
    find_neq(S,GC),
    !,
    %trace_irules('dom-neq_rel'),
    add_dom_neqd(RorF,S,D,AddedC,L,NewC),
    global_check2(RC,GC,NewC,F).
global_check2_dompf([C|RC],GC,[solved(dompf(S,D),(var(S),var(D)),[2|L]),
        size(S,N),size(D,N),integer(N)|NewC],F) :-
    is_dom_l(C,L,S,D,pfun),             % dompf-size: dompf(S,D) & size(S,N) --+-> dompf(S,D) & size(S,N) & size(D,N)
    var(S),var(D),\+member(2,L),
    find_size2(S,D,GC,N),
    !,
    %trace_irules('dompf-size'),
    global_check2(RC,GC,NewC,F).

global_check2_ran([C|RC],GC,[solved(ran(S,D),(var(S),var(D)),[1|L]),S neq {}|NewC],F) :-
    is_ran_l(C,L,S,D),                  % ran-neq: ran(S,D) & D neq {} --+-> ran(S,D) & D neq {} & S neq {}
    var(S),var(D),\+member(1,L),
    find_neq(D,GC),
    !,
    %trace_irules('ran_var-neq_ran'),
    global_check2(RC,GC,NewC,F).
global_check2_ran([C|RC],GC,[solved(ran(S,D),(var(S),var(D)),[1|L]),D neq {}|NewC],F) :- 
    is_ran_l(C,L,S,D),                  % ran-neq: ran(S,D) & S neq {} --+-> ran(S,D) & S neq {} & D neq {}
    var(S),var(D),\+member(1,L),
    find_neq(S,GC),
    !,
    %trace_irules('ran-neq_rel'),
    global_check2(RC,GC,NewC,F).
global_check2_ran([C|RC],GC,[solved(ran(S,D),var(S),[]),S neq {}|NewC],F) :-
    C = ran(S,D),                       % (noran_elim) ran-neq: ran(S,{...}) --+-> ran(S,{...}) & S neq {}
    noran_elim,
    var(S), nonvar(D),
    !,
    %trace_irules('ran_nonvar-neq_ran'),
    global_check2(RC,GC,NewC,F).

global_check2_un([C|RC],GC,AddedC,f) :- % un-rel/pfun: un(X,Y,Z) & rel(Z)/pfun(Z) --+-> ...
    is_un_l(C,L,X,Y,Z),
    var(X), var(Y), var(Z),
    \+ member(2,L), find_rel_pfun(Z,GC,RorF),
    !,
    %trace_irules('un-pfun-dom'),
    add_dom_un(RorF,X,Y,Z,AddedC,L,NewC),
    global_check2(RC,GC,NewC,f).
global_check2_un([C|RC],GC,AddedC,f) :- % un-rel/pfun: un(X,Y,Z) & rel(Z)/pfun(Z) --+-> ...
    is_un_l(C,L,X,Y,Z),
    var(X), var(Y), var(Z),
    \+ member(3,L), find_rel_pfun(Z,GC,RorF),
    !,
    %trace_irules('un-pfun-ran'),
    add_ran_un(RorF,X,Y,Z,AddedC,L,NewC),
    global_check2(RC,GC,NewC,f).

global_check2_un([C|RC],GC,[solved(un(X,Y,Z),(var(X),var(Y),var(Z)),[1|L]),
                        size(X,NX),size(Y,NY),size(Z,NZ),
                        integer(NX),integer(NY),integer(NZ)|NewC],F) :-
    \+size_solver_on,                   % (size_solver_on = false) un-size:
    is_un_l(C,L,X,Y,Z),                 % e.g., un(X,Y,Z) & size(Z,N) --+-> un(X,Y,Z) & size(Z,N) &
    var(X), var(Y), var(Z),             %                 size(X,NX) & size(Y,NY) & size(Z,NZ) &
    \+member(1,L), find_size3(X,Y,Z,GC,_), %              NX =< NZ & NY =< NZ & NX + NY >= NZ
    !,
    %trace_irules('un-size'),
    solve_int(NX =< NZ,IntC1),
    solve_int(NY =< NZ,IntC2),
    solve_int(NX + NY >= NZ,IntC3),
    append(IntC1,IntC2,IntC12), append(IntC12,IntC3,IntC),
    append(IntC,RC,R3),
    global_check2(R3,GC,NewC,F).

%%%%%%%%%%%%%%%%%%%%%%%%%%%% auxiliary predicates for global_check

is_sub_intv(subset(int(A,B),S),_,A,B,S).

is_un(un(X,Y,Z),_,X,Y,Z) :- !.
is_un(solved(un(X,Y,Z),_,Lev),Lev,X,Y,Z) :- !. 
is_un(delay(un(X,Y,Z),_),_,X,Y,Z).

is_un_l(un(X,Y,Z),[],X,Y,Z) :- !.
is_un_l(solved(un(X,Y,Z),_,Lev),Lev,X,Y,Z) :- !.   
is_un_l(delay(un(X,Y,Z),_),[],X,Y,Z).

is_sub(subset(X,Y),_,X,Y).

is_inters(inters(X,Y,Z),_,X,Y,Z).

is_diff(diff(X,Y,Z),_,X,Y,Z).

is_size(size(X,N),_,X,N) :- !.
is_size(solved(size(X,N),_,Lev),Lev,X,N) :- !.
%is_size(delay( (size(X,N) & true), _),_,X,N).

is_sum(sum(X,N),_,X,N) :- !.
is_sum(solved(sum(X,N),_,Lev),Lev,X,N).

is_min(smin(X,N),_,X,N) :- !.
is_min(solved(smin(X,N),_,Lev),Lev,X,N).

is_max(smax(X,N),_,X,N) :- !.
is_max(solved(smax(X,N),_,Lev),Lev,X,N).

is_neq(X neq Y,_,X,Y) :- !.
is_neq(solved(X neq Y,_,Lev),Lev,X,Y).

is_nin(X nin Y,_,X,Y).

is_in(X in Y,_,X,Y) :- !.
is_in(solved(X in Y,_,Lev),Lev,X,Y) :- !.

is_dom_l(dom(X,N),[],X,N,rel) :- !.
is_dom_l(solved(dom(X,N),_,L),L,X,N,rel) :- !.
is_dom_l(dompf(X,N),[],X,N,pfun) :- !.
is_dom_l(solved(dompf(X,N),_,L),L,X,N,pfun).

is_ran_l(ran(X,N),[],X,N) :- !.
is_ran_l(solved(ran(X,N),_,L),L,X,N).

is_inv(inv(X,Y),_,X,Y).

is_comp(comp(X,Y,Z),_,X,Y,Z) :- !.
is_comp(comppf(X,Y,Z),_,X,Y,Z) :- !.

is_id(id(X,Y),_,X,Y).

is_rel(rel(X),_,X).

is_pfun(pfun(X),_,X).

has_ris(RIS = E,_,D) :-
    ris_term(RIS,ris(_ in D,_,_,_,_)), var(D),
    nonvar(E), is_empty(E),!.
has_ris(_ nin RIS,_,D) :-
    ris_term(RIS,ris(_ in D,_,_,_,_)), var(D),!.

has_ris2(RIS1 = RIS2,_,D1,D2) :-
    ris_term(RIS1,ris(_ in D1,_,_,_,_)), var(D1),
    ris_term(RIS2,ris(_ in D2,_,_,_,_)), var(D2),!.

%%%%%% search a constraint in the CS (called with 2nd parm. GC)

find_setconstraint(X,cs(_,[C|_])) :-      % un(X,Y,Z) or un(ris(...),Y,Z) or un(cp(A,B),Y,Z) or ... is in the CS
    is_un_l(C,_,S1,S2,S3),
    var_ris_st(S1,S1Var), var_ris_st(S2,S2Var), var_ris_st(S3,S3Var),
    (X == S1Var,! ; X == S2Var,! ; X == S3Var),!.
find_setconstraint(X,cs(_,[C|_])) :-
    is_sub(C,_,S1,S2),                    % subset(X,Y) or subset(ris(...),Y) or subset(cp(A,B),Y) is in the CS
    var_ris_st(S1,S1Var), var_ris_st(S2,S2Var),
    (X == S1Var,! ; X == S2Var),!.
find_setconstraint(X,cs(_,[C|_])) :-
    is_sub(C,_,S1,_S2),                   % subset(X,t) or subset(ris(...),t) or subset(cp(A,B),t) is in the CS
    var_ris_st(S1,S1Var),
    X == S1Var,!.
find_setconstraint(X,cs(_,[C|_])) :-
    is_inters(C,_,S1,_S2,S3),             % inters(X,t,Z) or inters(ris(...),t,Z) or inters(cp(A,B),t,Z) is in the CS
    var_ris_st(S1,S1Var), var_ris_st(S3,S3Var),
    (X == S1Var,! ; X == S3Var),!.
find_setconstraint(X,cs(_,[C|_])) :-
    is_inters(C,_,_S1,S2,S3),             % inters(t,Y,Z) or inters(t,ris(...),Z) or inters(t,cp(A,B),Z) is in the CS
    var_ris_st(S2,S2Var), var_ris_st(S3,S3Var),
    (X == S2Var,! ; X == S3Var),!.
find_setconstraint(X,cs(_,[C|_])) :-      % size(X,n) or size(cp(A,B),n) is in the CS
    is_size(C,_,S1,_),
    var_ris_st(S1,S1Var),
    X == S1Var,!.
find_setconstraint(X,cs(_,[C|_])) :-
    is_diff(C,_,S1,S2,S3),               % diff(X,Y,Z) or diff(ris(...),Y,Z) or diff(cp(A,B),Y,Z) or ... is in the CS
    var_ris_st(S1,S1Var), var_ris_st(S2,S2Var), var_ris_st(S3,S3Var),
    (X == S1Var,! ; X == S2Var,! ; X == S3Var),!.
find_setconstraint(X,cs(_,[C|_])) :-
    is_dom_l(C,_,S1,S2,_),                % dom(X,Y) or dom(ris(...),Y) or dom(cp(A,B),Y) or ... is in the CS
    var_ris_st(S1,S1Var), var_ris_st(S2,S2Var),
    (X == S1Var,! ; X == S2Var),!.
find_setconstraint(X,cs(_,[C|_])) :-
    is_ran_l(C,_,S1,_S2),                 % ran(X,t) or ran(ris(...),t) or ran(cp(A,B),t)  is in the CS
    noran_elim,
    var_ris_st(S1,S1Var),
    X == S1Var,!.
find_setconstraint(X,cs(_,[C|_])) :-
    is_ran_l(C,_,S1,S2),                  % ran(X,t) or ran(ris(...),t) or ran(cp(A,B),t) or ... is in the CS
    var_ris_st(S1,S1Var), var_ris_st(S2,S2Var),
    (X == S1Var,! ; X == S2Var),!.
find_setconstraint(X,cs(_,[C|_])) :-
    is_inv(C,_,S1,S2),                    % inv(X,Y) inv(ris(...),Y) or inv(cp(A,B),Y) or ... is in the CS
    var_ris_st(S1,S1Var), var_ris_st(S2,S2Var),
    (X == S1Var,! ; X == S2Var),!.
find_setconstraint(X,cs(_,[C|_])) :-
    is_id(C,_,S1,S2),                     % id(X,Y) id(ris(...),Y) or id(cp(A,B),Y) or ... is in the CS
    var_ris_st(S1,S1Var), var_ris_st(S2,S2Var),
    (X == S1Var,! ; X == S2Var),!.
find_setconstraint(X,cs(_,[C|_])) :-
    is_comp(C,_,S1,_S2,S3),               % comp(X,t,Z) or comp(ris(...),t,Z) or comp(cp(A,B),t,Z) or ... is in the CS
    var_ris_st(S3,S3Var), var_ris_st(S1,S1Var),
    (X == S1Var,! ; X == S3Var),!.
find_setconstraint(X,cs(_,[C|_])) :-
    is_comp(C,_,_S1,S2,S3),               % comp(t,X,Z) or comp(t,ris(...),Z) or comp(t,cp(A,B),Z) or ... is in the CS
    var_ris_st(S3,S3Var), var_ris_st(S2,S2Var),
    (X == S2Var,! ; X == S3Var),!.
find_setconstraint(X,cs(_,[C|_])) :-
    is_comp(C,_,S1,_S2,S3),               % comp(X,t,{}) or comp(ris(...),t,{}) or comp(cp(A,B),t,{}) or ... is in the CS
    is_empty(S3), var_ris_st(S1,S1Var),
    X == S1Var,!.
find_setconstraint(X,cs(_,[C|_])) :-
    is_comp(C,_,_S1,S2,S3),               % comp(t,X,{}) or comp(t,ris(...),{}) or comp(t,cp(A,B),{}) or ... is in the CS
    is_empty(S3), var_ris_st(S2,S2Var),
    X == S2Var,!.
find_setconstraint(X,cs(_,[C|_])) :-
    has_ris(C,_,D),                       % ris(_,D,_,_,_) = {} or T nin ris(_,D,_,_,_), D var., is in the CS
    X == D,!.
find_setconstraint(X,cs(_,[C|_])) :-
    has_ris2(C,_,D1,D2),                  % ris(_,D1,_,_,_) = ris(_,D2,_,_,_), D1, D2 var., is in the CS
    (X == D1,! ; X == D2),!.
find_setconstraint(X,cs(Neqs,[_|R])) :-
    find_setconstraint(X,cs(Neqs,R)).

find_setconstraint(X,Y,cs(_,[C|_]),Z1,Z2) :-
    is_un(C,_,S1,S2,S3),                   % un(X,Y,Z) or un(ris(...),Y,Z) or un(cp(A,B),Y,Z) or ... is in the CS?
    var_ris_st(S1,S1Var), var_ris_st(S2,S2Var), var_ris_st(S3,S3Var),
    one_of3(X,Y,S1Var,S2Var,S3Var,Z1,Z2),!.
find_setconstraint(X,Y,cs(_,[C|_]),Z1,Z2) :-
    is_sub(C,_,S1,S2),                     % subset(X,Y) or subset(ris(...),Y) or subset(cp(A,B),Y) is in the CS?
    var_ris_st(S1,S1Var), var_ris_st(S2,S2Var),
    one_of2(X,Y,S1Var,S2Var,Z1,Z2),!.
find_setconstraint(X,Y,cs(_,[C|_]),Z1,Z2) :-
    is_sub(C,_,S1,_S2),                    % subset(X,t) or subset(ris(...),t) or subset(cp(A,B),t,Z) or is in the CS?
    var_ris_st(S1,S1Var),
    one_of1(X,Y,S1Var,Z1,Z2),!.
find_setconstraint(X,Y,cs(_,[C|_]),Z1,Z2) :-
    is_inters(C,_,S1,_S2,S3),              % inters(X,t,Z) or inters(ris(...),t,Z) or inters(cp(A,B),t,Z) or is in the CS?
    var_ris_st(S1,S1Var), var_ris_st(S3,S3Var),
    one_of2(X,Y,S1Var,S3Var,Z1,Z2),!.
find_setconstraint(X,Y,cs(_,[C|_]),Z1,Z2) :-
    is_inters(C,_,_S1,S2,S3),              % inters(X,t,Z) or inters(ris(...),t,Z) inters(cp(A,B),t,Z) or is in the CS?
    var_ris_st(S2,S2Var), var_ris_st(S3,S3Var),
    one_of2(X,Y,S2Var,S3Var,Z1,Z2),!.
find_setconstraint(X,Y,cs(_,[C|_]),Z1,Z2) :-  % size(X,n) or size(cp(A,B),n) is in the CS
    is_size(C,_,S1,_),
    var_ris_st(S1,S1Var),
    one_of1(X,Y,S1Var,Z1,Z2),!.
find_setconstraint(X,Y,cs(_,[C|_]),Z1,Z2) :-
    is_diff(C,_,S1,S2,S3),                   % diff(X,Y,Z) or diff(ris(...),Y,Z) or diff(cp(A,B),Y,Z) or ... is in the CS?
    var_ris_st(S1,S1Var), var_ris_st(S2,S2Var), var_ris_st(S3,S3Var),
    one_of3(X,Y,S1Var,S2Var,S3Var,Z1,Z2),!.
find_setconstraint(X,Y,cs(_,[C|_]),Z1,Z2) :-
    is_dom_l(C,_,S1,S2,_),                 % dom(X,Y) or dompf(Y,X) is in the CS?
    var_ris_st(S1,S1Var), var_ris_st(S2,S2Var),
    one_of2(X,Y,S1Var,S2Var,Z1,Z2),!.
find_setconstraint(X,Y,cs(_,[C|_]),Z1,Z2) :-
    is_ran_l(C,_,S1,_S2),                  % ran(X,Y) or ran(Y,X) is in the CS?
    noran_elim,
    var_ris_st(S1,S1Var),
    one_of1(X,Y,S1Var,Z1,Z2),!.
find_setconstraint(X,Y,cs(_,[C|_]),Z1,Z2) :-
    is_ran_l(C,_,S1,S2),                   % ran(X,Y) or ran(Y,X) is in the CS?
    var_ris_st(S1,S1Var), var_ris_st(S2,S2Var),
    one_of2(X,Y,S1Var,S2Var,Z1,Z2),!.
find_setconstraint(X,Y,cs(_,[C|_]),Z1,Z2) :-
    is_inv(C,_,S1,S2),                     % inv(X,Y) or inv(Y,X) is in the CS?
    var_ris_st(S1,S1Var), var_ris_st(S2,S2Var),
    one_of2(X,Y,S1Var,S2Var,Z1,Z2),!.
find_setconstraint(X,Y,cs(_,[C|_]),Z1,Z2) :-
    is_id(C,_,S1,S2),                      % id(X,Y) or id(Y,X) is in the CS?
    var_ris_st(S1,S1Var), var_ris_st(S2,S2Var),
    one_of2(X,Y,S1Var,S2Var,Z1,Z2),!.
find_setconstraint(X,Y,cs(_,[C|_]),Z1,Z2) :-
    is_comp(C,_,S1,_S2,S3),                % comp(X,t,Z) or comp(ris(...),t,Z) or comp(cp(A,B),t,Z) or ... is in the CS?
    var_ris_st(S3,S3Var), var_ris_st(S1,S1Var),
    one_of2(X,Y,S1Var,S3Var,Z1,Z2),!.
find_setconstraint(X,Y,cs(_,[C|_]),Z1,Z2) :-
    is_comp(C,_,_S1,S2,S3),                % comp(t,X,Z) or comp(t,ris(...),Z) or comp(t,cp(A,B),Z) or ... is in the CS?
    var_ris_st(S3,S3Var), var_ris_st(S2,S2Var),
    one_of2(X,Y,S2Var,S3Var,Z1,Z2),!.
find_setconstraint(X,Y,cs(_,[C|_]),Z1,Z2) :-
    is_comp(C,_,S1,_S2,S3),                % comp(X,t,{}) or comp(ris(...),t,{}) or comp(cp(A,B),t,{}) or ... is in the CS?
    is_empty(S3), var_ris_st(S1,S1Var),
    one_of1(X,Y,S1Var,Z1,Z2),!.
find_setconstraint(X,Y,cs(_,[C|_]),Z1,Z2) :-
    is_comp(C,_,_S1,S2,S3),                % comp(t,X,{}) or comp(t,ris(...),{}) or comp(t,cp(A,B),{}) or ... is in the CS?
    is_empty(S3), var_ris_st(S2,S2Var),
    one_of1(X,Y,S2Var,Z1,Z2),!.
find_setconstraint(X,Y,cs(_,[C|_]),Z1,Z2) :-
    has_ris(C,_,D),                        % ris(_,D,_,_,_) = {} or T nin ris(_,D,_,_,_), D var., is in the CS
    one_of1(X,Y,D,Z1,Z2),!.
find_setconstraint(X,Y,cs(_,[C|_]),Z1,Z2) :-
    has_ris2(C,_,D1,D2),                   % ris(_,D1,_,_,_) = ris(_,D2,_,_,_), D1, D2 var., is in the CS
    one_of2(X,Y,D1,D2,Z1,Z2),!.
find_setconstraint(X,Y,cs(Neqs,[_|R]),Z1,Z2) :-
    find_setconstraint(X,Y,cs(Neqs,R),Z1,Z2).

one_of3(X,Y,S1,_,_,X,Y) :- X == S1,!.
one_of3(X,Y,_,S2,_,X,Y) :- X == S2,!.
one_of3(X,Y,_,_,S3,X,Y) :- X == S3,!.
one_of3(X,Y,S1,_,_,Y,X) :- Y == S1,!.
one_of3(X,Y,_,S2,_,Y,X) :- Y == S2,!.
one_of3(X,Y,_,_,S3,Y,X) :- Y == S3.

one_of2(X,Y,S1,_,X,Y) :- X == S1,!.
one_of2(X,Y,_,S2,X,Y) :- X == S2,!.
one_of2(X,Y,S1,_,Y,X) :- Y == S1,!.
one_of2(X,Y,_,S2,Y,X) :- Y == S2.

one_of1(X,Y,S1,X,Y) :- X == S1,!.
one_of1(X,Y,S1,Y,X) :- Y == S1.

find_neq(Int,cs([I neq E|_],_)) :-
    nonvar(E), is_empty(E), I == Int,!.
find_neq(Int,cs([_|R],Others)) :-
    find_neq(Int,cs(R,Others)).

find_nin(X,cs(_,[C|_]),T) :-        % T nin X is in the CS
    is_nin(C,_,T,Y),
    X == Y,!.
find_nin(X,cs(Neqs,[_|R]),T) :-
    find_nin(X,cs(Neqs,R),T).

find_in(X,cs(_,[C|_]),T) :-         % T in X is in the CS
    is_in(C,_,T,Y),
    X == Y,!.
find_in(X,cs(Neqs,[_|R]),T) :-
    find_in(X,cs(Neqs,R),T).

find_size2(X,Y,cs(_,[C|_]),N) :-    % size(X,N) or size(Y,N) is in the CS
    is_size(C,_,S,N),
    (X == S,! ; Y == S),!.
find_size2(X,Y,cs(Neqs,[_|R]),M) :-
    find_size2(X,Y,cs(Neqs,R),M).

find_size3(X,Y,Z,cs(_,[C|_]),N) :-  % size(X,N) or size(Y,N) or size(Z,N) is in the CS
    is_size(C,_,S,N),
    (X == S,! ; Y == S,! ; Z == S),!.
find_size3(X,Y,Z,cs(Neqs,[_|R]),M) :-
    find_size3(X,Y,Z,cs(Neqs,R),M).

find_rel(X,cs(_,[C|_])) :-          % rel(X) is in the CS
    is_rel(C,_,Y),
    X == Y,!.
find_rel(X,cs(Neqs,[_|R])) :-
    find_rel(X,cs(Neqs,R)).

find_pfun(X,cs([C|_],_)) :-         % pfun(X) is in the CS
    is_pfun(C,_,Y),
    X == Y,!.
find_pfun(X,cs([_|R],Others)) :-
    find_pfun(X,cs(R,Others)).

find_rel_pfun(X,CS,RorF) :-         % either rel(X) or pfun(X) is in the CS
    (find_rel(X,CS),!, RorF=rel ; find_pfun(X,CS), RorF=pfun).

%%%%%% search a constraint in the rest of the CS (called with 2nd parm RC (from [C|RC]))

find_un2(X,Y,[C|_],S3) :-           % un(X,Y,_Z) or un(Y,X,_Z) is in the CS
    is_un_l(C,_,S1,S2,S3),
    (X == S1, Y == S2,! ; X == S2, Y == S1),!.
find_un2(X,Y,[_|R],S3) :-
    find_un2(X,Y,R,S3).

find_diff(X,Y,[C|_],S3) :-          % diff(X,Y,_Z) is in the CS
    is_diff(C,_,S1,S2,S3),
    X == S1, Y == S2,!.
find_diff(X,Y,[_|R],S3) :-
    find_diff(X,Y,R,S3).

find_size(X,[C|_],N) :-             % size(X,N) is in the CS
    is_size(C,_,S,N),
    X == S,!.
find_size(X,[_|R],M) :-
    find_size(X,R,M).

find_sum(X,[C|_],N) :-              % sum(X,N) is in the CS
    is_sum(C,_,S,N),
    X == S,!.
find_sum(X,[_|R],M) :-
    find_sum(X,R,M).

find_min(X,[C|_],N) :-              % smin(X,N) is in the CS
    is_min(C,_,S,N),
    X == S,!.
find_min(X,[_|R],M) :-
    find_min(X,R,M).

find_max(X,[C|_],N) :-              % smax(X,N) is in the CS
    is_max(C,_,S,N),
    X == S,!.
find_max(X,[_|R],M) :-
    find_max(X,R,M).

find_dom(X,[C|_],N) :-              % dom(X,N) is in the CS
    is_dom_l(C,_,S,N,_),
    X == S,!.
find_dom(X,[_|R],M) :-
    find_dom(X,R,M).

find_ran(X,[C|_],N) :-              % ran(X,N) is in the CS
    is_ran_l(C,_,S,N),
    X == S,!.
find_ran(X,[_|R],M) :-
    find_ran(X,R,M).

%%%%%% search and delete a constraint in the rest of the CS 
%%%%%% (called with 2nd parm RC (from [C|RC]))

find_del_sub_intv1(A,S,[subset(int(A1,C),S1)|RC],C,RC) :-  
    A == A1, S == S1,!.
find_del_sub_intv1(A,S,[Y|RC],C,[Y|RR]) :-  
    find_del_sub_intv1(A,S,RC,C,RR).
     
find_del_sub_intv2(B,S,[subset(int(C,B1),S1)|RC],C,RC) :-  
    B == B1, S == S1,!.
find_del_sub_intv2(B,S,[Y|RC],C,[Y|RR]) :-  
    find_del_sub_intv2(B,S,RC,C,RR).

%%%%%% checking type constraints

type_constr(C) :-
    (   p_type_constr(C) ->
        true
    ;
        n_type_constr(C) ->
        true
%    ;
%        C=delay(T,_), type_constr(T)
    ).

p_type_constr(set(_)).                      % positive type constraints
p_type_constr(integer(_)).
p_type_constr(rel(_)).
p_type_constr(pfun(_)).
p_type_constr(pair(_)).
%p_type_constr(bag(_)).
%p_type_constr(list(_)).

n_type_constr(nset(_)).                     % negative type constraints
n_type_constr(ninteger(_)).
n_type_constr(nrel(_)).
n_type_constr(npfun(_)).
n_type_constr(npair(_)).

no_type_error_all(_C,[]) :- !.
no_type_error_all(C,[B|R]) :-
    C =.. [F1,X], B =.. [F2,Y],
    X == Y, F1 \== F2, !,
    \+ check_type_error(F1,F2),
    no_type_error_all(C,R).
no_type_error_all(C,[_B|R]) :-
    no_type_error_all(C,R).

check_type_error(F1,F2) :-
    incompatible(F1,LInc),
    member(F2,LInc).

%incompatible(set,[nset,integer,bag,list]) :-!.
%incompatible(rel,[nset,integer,bag,list]) :-!.
%incompatible(pfun,[nset,npfun,integer,bag,list]) :-!.
%%incompatible(pair,[npair,set,rel,pfun,integer,bag,list]) :-!.
%incompatible(integer,[ninteger,set,rel,pfun,bag,list]) :-!.
%incompatible(bag,[set,rel,pfun,integer,list]) :-!.
%incompatible(list,[set,rel,pfun,integer,bag]) :-!.

incompatible(set,[nset,integer]) :-!.
incompatible(rel,[nset,integer]) :-!.
incompatible(pfun,[nset,npfun,integer]) :-!.
incompatible(integer,[ninteger,set,rel,pfun]) :-!.
incompatible(bag,[set,rel,pfun,integer]) :-!.
incompatible(list,[set,rel,pfun,integer]) :-!.

incompatible(nset,[set,rel,pfun]) :-!.
%incompatible(nrel,[rel,pfun]) :-!.
%incompatible(npfun,[pfun]) :-!.
%incompatible(npair,[pair]) :-!.
incompatible(ninteger,[integer]) :-!.

%%%%%% replacing constraints neq

mk_new_constr(W,T,OutC) :-             % W and T variables
    OutC = [N in W, N nin T].   
mk_new_constr(W,T,OutC) :-
    OutC = [N in T, N nin W].  
mk_new_constr(W,T,OutC) :-
    OutC = [W = {}, T neq {}].
%without the last clause a goal such as            
%solve(un(B,C,C) & B neq X) & call(X=a & B={})
%fails 

mk_new_constr2(W,T,OutC) :-             % W variable and T={} 
    nonvar(T), is_empty(T),!,
    W = M with _N, OutC = [set(M)].
mk_new_constr2(W,T,OutC) :-             % W variable and T non-variable set term  
    OutC = [N in W, N nin T].    
mk_new_constr2(W,T,OutC) :-
    OutC = [N in T, N nin W].    

%%%%%% adding dom and ran for relations/partial functions

add_dom_un(rel,X,Y,Z,AddedC,L,NewC) :-
    AddedC = [solved(un(X,Y,Z),(var(X),var(Y),var(Z)),[2|L]),
                        rel(X),rel(Y),dom(X,DX),dom(Y,DY),dom(Z,DZ),
                        un(DX,DY,DZ)|NewC].
add_dom_un(pfun,X,Y,Z,AddedC,L,NewC) :-
    AddedC = [solved(un(X,Y,Z),(var(X),var(Y),var(Z)),[2|L]),
                        pfun(X),pfun(Y),dompf(X,DX),dompf(Y,DY),dompf(Z,DZ),
                        un(DX,DY,DZ)|NewC].

add_ran_un(rel,X,Y,Z,AddedC,L,NewC) :-
   AddedC = [solved(un(X,Y,Z),(var(X),var(Y),var(Z)),[3|L]),
                        rel(X),rel(Y),ran(X,RX),ran(Y,RY),ran(Z,RZ),
                        un(RX,RY,RZ)|NewC].
add_ran_un(pfun,X,Y,Z,AddedC,L,NewC) :-
   AddedC = [solved(un(X,Y,Z),(var(X),var(Y),var(Z)),[3|L]),
                        pfun(X),pfun(Y),ran(X,RX),ran(Y,RY),ran(Z,RZ),
                        un(RX,RY,RZ)|NewC].

add_dom_neq(rel,S,D,AddedC,L,NewC) :-
    AddedC = [solved(dom(S,D),(var(S),var(D)),[1|L]),S neq {}|NewC].
add_dom_neq(pfun,S,D,AddedC,L,NewC) :-
    AddedC = [solved(dompf(S,D),(var(S),var(D)),[1|L]),S neq {}|NewC].

add_dom_neqd(rel,S,D,AddedC,L,NewC) :-
    AddedC = [solved(dom(S,D),(var(S),var(D)),[1|L]),D neq {}|NewC].
add_dom_neqd(pfun,S,D,AddedC,L,NewC) :-
    AddedC = [solved(dompf(S,D),(var(S),var(D)),[1|L]),D neq {}|NewC].

add_ran_size(S,R,M,N,AddedC,L,NewC) :-
    noran_elim,!,
    AddedC = [solved(ran(S,R),(var(S),var(R);var(S),nonvar(R),\+(is_empty(R))),[2|L]),
        size(S,N),size(R,M),integer(N),integer(M)|NewC].
add_ran_size(S,R,M,N,AddedC,L,NewC) :-
    AddedC = [solved(ran(S,R),(var(S),var(R)),[2|L]),
        size(S,N),size(R,M),integer(N),integer(M)|NewC].

%%%%% Creating a set of at least N distinct variables, e.g. {X_1,...,X_N/R} with X_1 neq X_2 & ... & X_N-1 neq X_N
mk_set_atleastN_var(N,T,Sfin,C) :-
   mk_set_atleastN_var(N,T,T,Sfin,C).
mk_set_atleastN_var(0,T,S,S,[set(T)]) :- !.
mk_set_atleastN_var(N,T,Sin,Sout,[X nin T|C]) :-
    M is N-1,
    all_diff_set_var(Sin,X,C1),

    %solve_int(M is N-1,IntC),
    %all_diff_set_var(Sin,X,NinC),
    %append(IntC,NinC,C1),

    mk_set_atleastN_var(M,T,Sin with X,Sout,C2),
    append(C1,C2,C).

all_diff_set_var(R,_,[]) :-
    var(R),!.
all_diff_set_var({},_,[]) :-!.
all_diff_set_var(R with Z,X,[X neq Z|CR]) :-
    all_diff_set_var(R,X,CR).


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%     Integer constraints
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

int_solver(Slv) :-
    b_getval(int_solver,Slv).

solve_int(Constr,NewC) :-        % solve the integer constraint 'Constr' using
    int_solver(clpfd),!,         % either the clp(FD) solver
    solve_FD(Constr,NewC).
solve_int(Constr,NewC) :-        % or the clp(q) solver
    int_solver(clpq),
    solve_Q(Constr,NewC).

add_intv_w(Constr,ConstrAll,Warning) :-   %(clp(FD)) add interval constraints X in D, if any
    int_solver(clpfd),!,               % Warning is 'not_finite_domain' if at least one is found,
    add_FDc(Constr,ConstrAll,Warning), % and labelling is on; otherwise Warning is unbound
    fd_warning(Warning).               % (clp(FD)) if Warning is on, print a warning msg
add_intv_w(Constr,Constr,_).

labeling(X) :-
    int_solver(clpfd),!,
    labeling_FD([X]).
labeling(X) :-
    int_solver(clpq),!,
    labeling_Q(X).

is_int_var(X) :-
    int_solver(clpfd),!,
    is_fd_var(X).
is_int_var(X) :-
    attvar(X).

check_int_constr(X,Y) :-
    int_solver(clpfd),!,
    check_fd_constr(X,Y).
check_int_constr(X,Y) :-
    check_q_constr(X,Y).

finalize_int_constr(C,LIntVars) :-
    int_solver(clpfd),!,
    check_domain(C,LIntVars),
    labeling_FD(LIntVars).
finalize_int_constr(C,LIntVars) :-
    %int_solver(clpq),
    check_int_solutions(C,LIntVars).

minimize(_C,N,M) :-
    int_solver(clpfd),!,
    minimize_FD(N),
    nb_getval(min,M).
minimize(C,N,M) :-
    int_solver(clpq),!,
    collect_integer(C,LIntVars),
    %DBG write('integer vars: '),write(LIntVars),nl,
    bb_inf(LIntVars,N,M,_).


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%     clp(FD) constraints
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

:- use_module(library(clpfd)).

solve_FD(Constr,NewC) :-        % Solve the constraint 'Constr' using the CLP(FD) solver
    %%%DBG write(solve_FD(Constr)),nl,
    tau(Constr,FD_Constr,NewC),
    %catch(call(FD_Constr),Msg,excpt_action(Msg)).
    call(FD_Constr).   

fd_expr(X,E) :-
    X #= E.

tau(X is E,X #= E,[glb_state(X is E)]).   % The translation function: from SET constraints to FD
tau(X =< Y,X #=< Y,[glb_state(X =< Y)]).  % constraints, and vice versa
tau(X >= Y,X #>= Y,[glb_state(X >= Y)]).
tau(X < Y,X #< Y,[glb_state(X < Y)]).
tau(X > Y,X #> Y,[glb_state(X > Y)]).
tau(X neq T,X #\= T,[]).
tau(T in int(A,B),T in A..B,[]) :- !.  
tau(T in D,T in D,[]).

is_fd_var(X) :-
    clpfd:fd_var(X).

get_domain(X,(X in D)) :-          % get_domain(X,FDc): true if X is a variable and
    var(X),                        % FDc is the interval membership constraint for X
    clpfd:fd_dom(X,D).

labeling_FD(L) :-
    labeling_FD(L,R),
    fd_labeling_strategy(Str),
    clpfd:labeling(Str,R).

labeling_FD(_,[]) :-               % if nolabel, do nothing
    nolabel,!.
labeling_FD([],[]) :- !.           % if no var., do nothing
labeling_FD([X|L],R) :-            % if the variable X has a domain associated with it,
    get_domain(X,X in D),!,        % then X is added to variables that must be instantiated
    labeling1(X,D,R1),
    labeling_FD(L,R2),
    append(R1,R2,R).
labeling_FD([_X|L],R) :-
    labeling_FD(L,R).              % otherwise, X is ignored

labeling1(_X,inf.._B,[]) :- !.     % e.g., X in inf..1  --> no labeling
labeling1(_X,_A..sup,[]) :- !.     % e.g., X in 1..sup  --> no labeling
labeling1(X,(I) \/ (A..sup),R) :-  % e.g., X in (inf..2)\/(4..5)\/(7..9)\/(11..sup)
    first_int(I,inf..B,J),!,       % --> labeling on the bounded part
    (   X in J, R=[X]
    ;   X in (inf..B), R=[]
    ;   X in (A..sup), R=[]
    ).
labeling1(X,(I) \/ (A..sup),R) :- !, % e.g., X in (1..2)\/(4..5)\/(7..sup)
    (   X in I, R=[X]                % --> labeling on the bounded part
    ;   X in (A..sup), R=[]
    ).
labeling1(X,(I) \/ (In),R) :-      % e.g., X in (inf..2)\/(4..5)\/(7..9)
    first_int(I,inf..B,J),!,       % --> labeling on the bounded part
    (   X in (J) \/ (In), R=[X]
    ;   X in (inf..B), R=[]
    ).
labeling1(X,_D,[X]).               % e.g., X in (1..2)\/(4..5)\/(7..9)

first_int((A .. B),(A .. B),(1 .. 0)) :- !.      % first_int(+Int,?Rest,?First)
first_int((I) \/ (In),I0,(IRest) \/ (In)) :-     % 'Int' is a disj. of intervals and
    first_int(I,I0,IRest).                    % 'First' is the first disjunct
                                                 % 'Rest' the remaining part

%add_FDc(SETc,SETFDc,R)
%SETFDc is the list of contraints obtained from the list of constraints SETc
%by replacing all integer constraints integer(X) with the domain constraint
% X in D, where D is the FD domain of X (unless D is int(inf,sup)).
%R is either 'not_finite_domain' if at least one such integer constraint is found
%and labeling is on; otherwise, R is uninitialized

add_FDc([],[],_) :- !.
add_FDc([C|SETc],[C|FDc],Warning) :-
    C \= integer(_), !,
    add_FDc(SETc,FDc,Warning).
add_FDc([integer(X)|SETc],[integer(X)|FDc],Warning) :-
    \+ is_fd_var(X), !,
    add_FDc(SETc,FDc,Warning).
add_FDc([integer(X)|SETc],FDc,Warning) :-
    get_domain(X,FD),
    tau(X in D,FD,_),
    (   nolabel ->
        true
    ;
        Warning = 'not_finite_domain'
    ),
    (   D == int(inf,sup) ->
        FDc = [integer(X)|FDcCont]
    ;
        FDc = [(X in D),integer(X)|FDcCont]
    ),
    add_FDc(SETc,FDcCont,Warning).

fd_warning(R) :-
    var(R),!.
fd_warning(_) :-
    print_single_warning('***WARNING***: non-finite domain').

check_fd_constr(X,Y) :-            % if X is an integer variable
    is_int_var(X),!,               % then Y must be a simple_integer_expr;
    simple_integer_expr(Y).
check_fd_constr(_X,_Y).

check_domain(C,[X|L]) :-                  %to collect all integer variables that are
    memberrest(integer(X),C,CRest),!,     %still uninstantiated in the constraint C
    check_domain(CRest,L).
check_domain(_,[]).

minimize_FD(N) :-
    nat_try(N,M),
    nb_setval(min,M),
    fail.
minimize_FD(_N).

nat_try(N,X) :-
    nat_num(0,X),
    N #= X,!.

nat_num(N,N).
nat_num(N,M) :-
     N1 is N+1,
     nat_num(N1,M).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%     clp(Q) constraints
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

:- use_module(library(clpq)).

solve_Q(Constr,NewC) :-             % solve the constraint 'Constr' using the CLP(Q) solver
    %%%DBG write(solve_Q(Constr)),nl,
    rho(Constr,Q_Constr,NewC),
    %%%DBG write(rho(Constr,Q_Constr,NewC)),nl,
    %catch(call(Q_Constr),Msg,excpt_action(Msg)).  
    call(Q_Constr). 

q_expr(X,E) :-
    {X = E}.

rho(X is E,{CLPq_constr},[glb_state(X is E)]) :- !,
    CLPq_constr = (X = E).
    %write('CLPQ : '),write(CLPq_constr),nl.
rho(X =< Y,{CLPq_constr},[glb_state(X =< Y)|NewC]) :- !,
    norm(X =< Y,CLPq_constr,NewC).
    %write('CLPQ : '),write(CLPq_constr),nl.
rho(X >= Y,{CLPq_constr},[glb_state(X >= Y)|NewC]) :- !,
    norm(X >= Y,CLPq_constr,NewC).
    %write('CLPQ : '),write(CLPq_constr),nl.
rho(X < Y,{CLPq_constr},[glb_state(X < Y)|NewC]) :- !,
    norm(X < Y,CLPq_constr,NewC).
    %write('CLPQ : '),write(CLPq_constr),nl.
rho(X > Y,{CLPq_constr},[glb_state(X > Y)|NewC]) :- !,
    norm(X > Y,CLPq_constr,NewC).
    %write('CLPQ : '),write(CLPq_constr),nl.
%rho(X neq Y,{X =\= Y},[]) :- !.
rho(X neq Y,{CLPq_constr1 ; CLPq_constr2},NewC) :- !,
    norm(X < Y,CLPq_constr1,NewC1),
    norm(X > Y,CLPq_constr2,NewC2),
    append(NewC1,NewC2,NewC).
    %write('CLPQ : '),write(neq(CLPq_constr1,CLPq_constr2)),nl.
rho(T in int(A,B),{CLPq_constr1,CLPq_constr2},[glb_state(T >= A),glb_state(T =< B)|NewC]) :- !,
    norm(T >= A,CLPq_constr1,NewC1),
    norm(B >= T,CLPq_constr2,NewC2),
    append(NewC1,NewC2,NewC).
    %write('CLPQ : '),write(in(CLPq_constr1,CLPq_constr2)),nl.
rho(T in D,T in D,[]).

norm((C1,RC),NormC,NewC) :- !,       %first clause: not used
    single_norm(C1,NormC1,NewC1),
    norm(RC,NormRC,NewC2),
    qconstr_app(NormC1,NormRC,NormC),
    append(NewC1,NewC2,NewC).
norm((C1),NormC,NewC) :-
    single_norm(C1,NormC,NewC).

%single_norm(N>M,(N>M),[]) :-  
%    integer(N),integer(M),!.
single_norm(X>Y,(X=Y+K,K>=1),[integer(K)]) :-
    var(X),var(Y),!.
single_norm(X>N,(X=N+K,K>=1),[integer(K)]) :-
    var(X),integer(N),!.
single_norm(X>E,(X=Z+K,K>=1,Z=E),[integer(Z),integer(K)]) :-
    var(X),!.
single_norm(N>Y,(Y=N-K,K>=1),[integer(K)]) :-
    var(Y),integer(N),!.
single_norm(E>Y,(Y=Z-K,K>=1,Z=E),[integer(Z),integer(K)]) :-
    var(Y),!.
single_norm(E1>E2,(Z1=Z2+K,K>=1,Z1=E1,Z2=E2),[integer(Z1),integer(Z2),integer(K)]) :-!.
%
single_norm(X>=Y,(X=Y+K,K>=0),[integer(K)]) :-
    var(X),var(Y),!.
single_norm(X>=N,(X=N+K,K>=0),[integer(K)]) :-
    var(X),integer(N),!.
single_norm(X>=E,(X=Z+K,K>=0,Z=E),[integer(Z),integer(K)]) :-
    var(X),!.
single_norm(N>=Y,(Y=N-K,K>=0),[integer(K)]) :-
    var(Y),integer(N),!.
single_norm(E>=Y,(Y=Z-K,K>=0,Z=E),[integer(Z),integer(K)]) :-
    var(Y),!.
single_norm(E1>=E2,(Z1=Z2+K,K>=0,Z1=E1,Z2=E2),[integer(Z1),integer(Z2),integer(K)]) :- !.
%
single_norm(E1<E2,NormC,NewC) :- !,
    single_norm(E2>E1,NormC,NewC).
single_norm(E1=<E2,NormC,NewC) :- !,
    single_norm(E2>=E1,NormC,NewC).

qconstr_app((C1,R1),B,(C1,R3)) :- !,
    qconstr_app(R1,B,R3).
qconstr_app((C1),B,(C1,B)).

check_int_solutions(C,LIntVars) :-
    collect_integer(C,LIntVars),
    bb_inf_all(LIntVars,LIntVars,_,_).

collect_integer(C,LIntVars) :-             %to collect in LIntVars all attributed variables
    memberrest(integer(X),C,CRest),!,      %that are constrained to be of sort integer
    collect_integer_test(X,LIntVars1,LIntVars),
    collect_integer(CRest,LIntVars1).
collect_integer(_,[]).

collect_integer_test(X,LIntVars,[X|LIntVars]) :-
    attvar(X),!.
collect_integer_test(_X,LIntVars,LIntVars).

%bb_inf_all([],_) :- !.
%bb_inf_all(L,_X) :-
%     bb_inf(L,1,_,_).

% the third argument is here due to
% errors in CLP(Q). when CLP(Q) gets
% fixed this argument can be removed.
% so the third clause
% minimizing a sum instead of a variable
% is there due to the same errors in CLP(Q)
bb_inf_all([],_,_,_) :- !.
bb_inf_all(L,[X|_R],S,V) :-
    var(S),
    bb_inf_single(L,X,X,V),!.
bb_inf_all(L,[X|_R],S,V) :-
    nonvar(S),
    bb_inf_single(L,X,S,V),!.
bb_inf_all(L,[_X|R],S,V) :-
    bb_inf_all(L,R,S,V).

bb_inf_single(L,X,S,V) :-
    {X>=0},bb_inf(L,S,_,V).
bb_inf_single(L,X,S,V) :-
    {X =< -1},bb_inf(L,-S,_,V).

labeling_Q(_) :-                   % if nolabel, do nothing
    nolabel,!.
labeling_Q(X) :-                     
     bb_inf([X],X,Min,_V1),        % if the variable X has a closed domain then use it
     bb_inf([X],-X,NMax,_V2),!,    % otherwise do nothing    
     Max is -NMax,
     all_int(X,Min,Max).
labeling_Q(_).

all_int(M,M,M) :- !.
all_int(Min,Min,_Max).
all_int(X,Min,Max) :-
    Min1 is Min+1,
    all_int(X,Min1,Max).

check_q_constr(X,Y) :-            % if X is an integer variable
    attvar(X),!,                  % then Y must be a simple_integer_expr;
    simple_integer_expr(Y).
check_q_constr(_X,_Y).


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%     Program defined constraints
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

isetlog((true :- true),sys) :-!.
isetlog((less(A,X,C) :-
    A = C with X & set(C) & X nin C & 
    true),sys) :-!.
isetlog((nsubset(A,B) :-
    set(A) & set(B) & 
    X in A & X nin B & 
    true),sys) :-!.
isetlog((ninters(A,B,C) :-
    set(A) & set(B) & set(C) &
    (X in C & X nin A & true or
     X in C & X nin B & true or
     X in A & X in B & X nin C) & 
     true),sys) :-!.
isetlog((ndiff(A,B,C) :-
    set(A) & set(B) & set(C) & set(D) &
    diff(A,B,D) & D neq C & 
    true),sys) :-!.
isetlog((sdiff(A,B,C) :-
    set(A) & set(B) & set(C) & set(D) & set(E) &
    diff(A,B,D) & diff(B,A,E) & un(D,E,C) & 
    true),sys) :-!.

isetlog((nsize(A,N) :-
    set(A) & integer(N) &
    size(A,T) & T neq N & 
    true),sys) :-!.

isetlog((A =:= B :-
    X is A & Y is B & X = Y & 
    true),sys) :-!.
isetlog((A =\= B :-
    X is A & Y is B & X neq Y & 
    true),sys) :-!.

isetlog((rimg(R,A,B) :-
    set(A) & set(B) & rel(R) & 
    dres(A,R,RA) & ran(RA,B) & 
    true),sys)  :-!.
isetlog((applyTo(F,X,Y) :-
    F = F1 with [X,Y] & delay([X,Y] nin F1,false) & 
    comp({} with [X,X],F1,{}) & rel(F1) & 
    true),sys)  :-!.

% A implies B equivalent to not(A) or B   
isetlog((A implies B :-
    prolog_call(negate(A,NegA)) &
    (call(NegA) or call(B)) & 
    true),sys) :-!.
% A nimplies B equivalent to A & not(B)  
isetlog((A nimplies B :-
    prolog_call(negate(B,NegB)) &
    call(A) & call(NegB) & 
    true),sys) :-!.

% neg(A) 
isetlog((neg(A) :-
    prolog_call(negate(A,NegA)) &
    call(NegA) &
    true),sys) :-!.

% bool(V,F) returns the truth value of F in V
% (F & V = true) or (neg(F) & V = false).
isetlog((bool(V,F) :-
    prolog_call(negate(F,NegF)) &
    (call(F) & call(V = true) or call(NegF) & call(V = false)) &
    true),sys) :-!.


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%                              %%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%     Pre / post-processor     %%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%                              %%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% Exported predicates:
%
%             preproc_goal/2,
%             preproc/3,
%             postproc/2,
%             transform_goal/2,
%             transform_clause/2,
%             is_ker/1,
%             is_sf/3

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%     Preprocessing
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%%%%%%%%%%%%% Set (multiset) preprocessor:
%%%%%%%%%%%%% from {...} (*({...})) to 'with' ('mwith') notation
%%%%%%%%%%%%% from {...} to 'with' notation

preproc_goal(G,PGext) :-
    preproc(G,PG,TypeCL),
    norep_in_list(TypeCL,TypeCLRid),
    list_to_conj(TypeCC,TypeCLRid),
    conj_append(PG,TypeCC,PGext).

preproc_clause(Cl,(PA :- PBext)) :-
    preproc(Cl,(PA :- PB),TypeCL),
    norep_in_list(TypeCL,TypeCLRid),
    list_to_conj(TypeCC,TypeCLRid),
    conj_append(PB,TypeCC,PBext).

%%%%%%%%% proproc terms

preproc(X,X,[]) :-           % var
    var(X),!.
preproc(X,X,[]) :-           % constant terms
    atomic(X),!.
preproc(X,Y1,C) :-           % set terms
    is_set_ext(X),!,
    set_preproc(X,Y,C),
    norep_in_set(Y,Y1).
preproc(X,Y,C) :-            % interval terms
    int_term(X),!,
    int_preproc(X,Y,C).
preproc(X,Y,C) :-            % RIS terms
    is_ris_ext(X),!,
    ris_preproc(X,Y,C).
preproc(X,Y,C) :-            % CP terms
    cp_term(X),!,
    cp_preproc(X,Y,C).

%%%%%%%%% proproc conjunctions, disjunctions, clauses

preproc((A & B),(A1 & B1),C) :- 
    !, preproc(A,A1,C1), preproc(B,B1,C2),
    append(C1,C2,C).
%preproc((A or B),(A1 or B1),C) :-     
%    !, preproc(A,A1,C1), preproc(B,B1,C2),
%    append(C1,C2,C).
preproc((A or B),(Aext or Bext),[]) :-
    !, preproc(A,A1,TypeA1), preproc(B,B1,TypeB1), 
    norep_in_list(TypeA1,TypeA1Rid),
    list_to_conj(TypeA1Conj,TypeA1Rid),
    conj_append(A1,TypeA1Conj,Aext),
    norep_in_list(TypeB1,TypeB1Rid),
    list_to_conj(TypeB1Conj,TypeB1Rid),
    conj_append(B1,TypeB1Conj,Bext).
preproc((A :- B ),(A1 :- B1 ),C) :-
    !, preproc(A,A1,C1), preproc(B,B1,C2),
    append(C1,C2,C).

%%%%%%%%% proproc atomic predicates

%%%% quantifiers
preproc(X,Y,C) :-
    is_foreach(X,Y,C),!.
preproc(X,Y,C) :-
    is_nforeach(X,Y,C),!.
preproc(X,Y,C) :-
    is_exists(X,Y,C),!.
preproc(X,Y,C) :-
    is_nexists(X,Y,C),!.
preproc(X,Y,C) :-    
    is_let(X,Y,C),!.
preproc(X,Y,C) :-   
    is_nlet(X,Y,C),!.

%%%% negation (not strictly necessary - could be done by the last clause for 'all other predicates')
preproc(neg A,neg(A1),C) :-     
    !, preproc(A,A1,C).        % preproc instead of preproc_goal to put sort constraints outside negation
preproc(naf A,naf(A1),C) :-    
    !, preproc(A,A1,C).
%preproc(cneg A,cneg(A1),C) :- % for internal use only
%    !, preproc(A,A1,C).

%%%% meta-predicates
preproc(prolog_call(G),prolog_call(G),[]) :- 
    !.
preproc(call(A),call(A1),[]) :-
    !, preproc_goal(A,A1).
preproc(call(A,C),call(A1,C),[]) :-
    !, preproc_goal(A,A1).
preproc(solve(A),solve(A1),[]) :-
    !, preproc_goal(A,A1).
preproc((A)!,(A1)!,[]) :-
    !, preproc_goal(A,A1).
preproc(delay(A,G),delay(A1,G1),[]) :-   
    !, preproc_goal(A,A1),
    preproc_goal(G,G1).

%%%% all other predicates 
preproc(X,Z,C) :-
    nonvar(X),
    functor(X,F,_A),
    =..(X,[F|ListX]),
    preproc_all(ListX,ListZ,C1),
    =..(Z,[F|ListZ]),
    (   gen_type_constrs(Z,TypeC) ->
        append(C1,TypeC,C)
    ;
        C1 = C
    ).

preproc_all([],[],[]).
preproc_all([A|L1],[B|L2],C) :-
    preproc(A,B,C1),
    preproc_all(L1,L2,C2),
    append(C1,C2,C).

%%%%%%%%%%%%%%%%%% set preprocessing

set_preproc({},{},[]) :- !.
set_preproc(X with A,X with B,[set(X)|Constrs]) :-
    var(X),!, preproc(A,B,Constrs).
set_preproc(X with A,Y with B,Constrs) :-
    is_rest_ext(X),!,
    preproc(A,B,Constrs1), preproc(X,Y,Constrs2),
    append(Constrs1,Constrs2,Constrs).
set_preproc({}(A),B,Constrs) :-
    set_preproc_elems(A,B,Constrs),!.
set_preproc(_,_,_) :-
    msg_sort_error(set).    

set_preproc_elems(A,{} with A,[]) :-
    var(A), !.
set_preproc_elems((A1,B1),B2 with A2,Constrs) :- !,
    preproc(A1,A2,Constrs1),
    set_preproc_elems(B1,B2,Constrs2),
    append(Constrs1,Constrs2,Constrs).
set_preproc_elems(S,WT,Constrs) :-
    aggr_comps_ext(S,_A,_X),!,
    set_preproc_set(S,WT,Constrs).
set_preproc_elems(A1,{} with A2,Constrs) :-
    preproc(A1,A2,Constrs).

set_preproc_set(S,X with B,[set(X)|Constrs]) :-
    aggr_comps_ext(S,A,X),
    var(X),!,
    preproc(A,B,Constrs).
set_preproc_set(S,Y with B,Constrs) :-
    aggr_comps_ext(S,A,X),
    is_rest_ext(X),!,
    preproc(A,B,Constrs1), preproc(X,Y,Constrs2),
    append(Constrs1,Constrs2,Constrs).

is_rest_ext(X) :-
    is_set_ext(X),!.
is_rest_ext(X) :-
    int_term(X),!.
is_rest_ext(X) :-
    is_ris_ext(X),!.
is_rest_ext(X) :-
    cp_term(X).

%%%%%%%%%%%%%%%%%% interval preprocessing

int_preproc(int(A,B),{},[]) :-                 % int(a,b), b < a --> {}
    integer(A), integer(B),
    B < A,!.
int_preproc(I,I,C) :-       
    is_int(I,C),!.
int_preproc(_,_,_) :-
    msg_sort_error(int).   

is_int(int(A,B),C2) :-                         % is_int(I) is true if I is a term that denotes an interval
    (var(A),C1=[integer(A)],! ; integer(A)),
    (var(B),C2=[integer(B)|C1],! ; integer(B)).   

%%%%%%%%%%%%%%%%%% ris preprocessing

%ris_preproc(+ris,-ris/set,-constraint).
ris_preproc(RisE,{},C) :-
    is_ris(RisE,ris(CE_Dom,V,Fl,P,PP)),
    nonvar(Fl),Fl==false,
    nonvar(CE_Dom), CE_Dom = (CtrlExpr in Dom),
    preproc(Dom,Dom1,C),
    check_ris(ris(CtrlExpr in Dom1,V,Fl,P,PP)),!.
ris_preproc(RisE,Dom1,C) :-
    is_ris(RisE,ris(CE_Dom,V,Fl,P,PP)),
    nonvar(Fl),Fl==true,
    nonvar(CE_Dom), CE_Dom = (CtrlExpr in Dom), var(CtrlExpr), CtrlExpr==P,
    preproc(Dom,Dom1,C),
    check_ris(ris(CtrlExpr in Dom1,V,Fl,P,PP)),!.
ris_preproc(RisE,{},[]) :-
    is_ris(RisE,ris(CE_Dom,_V,_F,_P,_PP)),
    nonvar(CE_Dom), CE_Dom = (_CtrlExpr in Dom),
    nonvar(Dom),is_empty(Dom),!.
ris_preproc(RisE,ris(New_CE_Dom,V,New_Fl,New_P,New_PP),C) :-
    ris_preproc_gen(RisE,ris(New_CE_Dom,V,New_Fl,New_P,New_PP),C),!.
ris_preproc(_,_,_) :-
    msg_sort_error(ris).   

ris_preproc_gen(RisE,ris(New_CE_Dom,V,New_Fl,New_P,New_PP),C) :-
        is_ris(RisE,ris(CE_Dom,V,Fl,P,PP)),
        preproc(CE_Dom,New_CE_Dom,C1),
        preproc(Fl,New_Fl,C2),
        preproc(P,New_P,C3),
        preproc(PP,Aux_PP,C4),
        check_ris(ris(New_CE_Dom,V,New_Fl,New_P,Aux_PP)),
        append(C1,C2,C12), append(C12,C3,C0),
        %CE_Dom = (CtrlExpr in _Dom),
        New_CE_Dom = (CtrlExpr in _Dom),   
        ctrl_expr(CtrlExpr,V,LV,_CtrlExprNew),
        separate_sortc_LV(C0,LV,C,LC),
        append(LC,C4,LC_C4),
        norep_in_list(LC_C4,Local_sortc),
        %DBG write('***LV***'),write(LV),nl,
        %DBG write('***C***'),write(C),nl,
        %DBG write('***Local_sortc***'),write(Local_sortc),nl,
        list_to_conj(Sort_PP,Local_sortc),
        conj_append(Aux_PP,Sort_PP,New_PP).

is_ris(ris(CE_Dom,Fl),RisTerm) :-                                     % ris/2 --> ris/5 (no parms)
    nonvar(CE_Dom), CE_Dom = (CtrlExpr in _),
    is_ris(ris(CE_Dom,[],Fl,CtrlExpr,true),RisTerm).
is_ris(ris(CE_Dom,LVars,Fl),RisTerm) :-                               % ris/3 --> ris/5
    nonvar(CE_Dom), CE_Dom = (CtrlExpr in _),
    is_list(LVars), !,
    is_ris(ris(CE_Dom,LVars,Fl,CtrlExpr,true),RisTerm).
is_ris(ris(CE_Dom,Fl,P),RisTerm) :-                                   % ris/3 --> ris/5 (no parms)
    is_ris(ris(CE_Dom,[],Fl,P,true),RisTerm).
is_ris(ris(CE_Dom,LVars,Fl,P),RisTerm) :-                             % ris/4 --> ris/5
    is_list(LVars), !,
    is_ris(ris(CE_Dom,LVars,Fl,P,true),RisTerm).
is_ris(ris(CE_Dom,Fl,P,PP),RisTerm) :-                                % ris/4 --> ris/5 (no parms)
    is_ris(ris(CE_Dom,[],Fl,P,PP),RisTerm).
is_ris(ris(CE_Dom,LVars,Fl,P,PP),ris(CE_Dom,LVars,Fl,P,PP)).

check_ris(ris(CE_Dom,LVars,_Fl,_P,_PP)) :-
    nonvar(CE_Dom), CE_Dom = (CtrlExpr in A),
    ctrl_expr_ok(CtrlExpr),
    (var(A),! ; aggr_term(A)),
    is_list(LVars).

%ctrl_expr_ok(X0) :-   
%    var(X0),!.
%ctrl_expr_ok([X0,Y0]) :-
%    var(X0), var(Y0),!.
%ctrl_expr_ok([X0|Y0]) :-
%    var(X0), var(Y0),!.
%ctrl_expr_ok(Y0 with X0) :-
%    var(X0), var(Y0).
ctrl_expr_ok(CT) :-
     ctrl_expr(CT,[],_,_).

separate_sortc_LV([],_LV,[],[]).
separate_sortc_LV([A|C0_Rest],LV,C,[A|Local_sortc]) :-
    type_constr(A),
    extract_vars(A,AVars),
    ndisj(AVars,LV),!,
    separate_sortc_LV(C0_Rest,LV,C,Local_sortc).
separate_sortc_LV([A|C0_Rest],LV,[A|C_Rest],Local_sortc) :-
    separate_sortc_LV(C0_Rest,LV,C_Rest,Local_sortc).

ndisj([X|_R],L) :-
    member_strong(X,L),!.
ndisj([_X|R],L) :-
    ndisj(R,L).

%%%%%%%%%%%%%%%%%% foreach/exist preprocessing               

is_foreach(foreach(D,Fo),FE4,C) :- !,     %foreach(V in D,F) or foreach([V in D,...],F) ---> foreach/4 
    is_foreach(foreach(D,[],Fo,true),FE4,C).
is_foreach(foreach(D,P,Fo,FP),foreach(D1,P,Fo1,FP1),C) :-
    nonvar(D), D = (V in _Dom),!,     
    ris_preproc_gen(ris(D,P,Fo,V,FP),ris(D1,_P,Fo1,_V,FP1),C).
is_foreach(foreach(D,P,Fo,FP),FEnew,C) :-
    nonvar(D), D = [_|_],                        % nested foreach
    unfold_nested_foreach(foreach(D,P,Fo,FP),FEflat),
    is_foreach(FEflat,FEnew,C).

is_nforeach(nforeach(D,Fo),NFE4,C) :- !,  %nforeach(V in D,F) or nforeach([V in D,...],F) ---> nforeach/4  
    is_nforeach(nforeach(D,[],Fo,true),NFE4,C).
is_nforeach(nforeach(D,P,Fo,FP),nforeach(D1,P,Fo1,FP1),C) :-
    nonvar(D), D = (V in _Dom),!,     
    ris_preproc_gen(ris(D,P,Fo,V,FP),ris(D1,_P,Fo1,_V,FP1),C).
% nforeach([X in A,Y in B],Fo) --> nforeach(X in A,foreach(X in B,Fo))
% nforeach([X in A,Y in B],[Z],Fo,FP) --> 
%   nforeach(X in A,[],foreach(X in B,[Z],Fo,FP),true)
% i.e. we first unfold as if it were a foreach
% and then we return to a nforeach
is_nforeach(nforeach(D,P,Fo,FP),NFEnew,C) :-
    nonvar(D), D = [_|_],      % proper nested foreach
    unfold_nested_foreach(foreach(D,P,Fo,FP),foreach(D1,P1,Fo1,FP1)),
    is_nforeach(nforeach(D1,P1,Fo1,FP1),NFEnew,C).

% foreach([X in A,Y in B],Fo) --> foreach(X in A,foreach(X in B,Fo))
% foreach([X in A,Y in B],[Z],Fo,FP) --> 
%   foreach(X in A,[],foreach(X in B,[Z],Fo,FP),true)
unfold_nested_foreach(foreach([D],P,Fo,FP),foreach(D,P,Fo,FP)) :- !.
unfold_nested_foreach(foreach([D|RD],P,Fo,FP),foreach(D,[],Fo1,true)) :-
    unfold_nested_foreach(foreach(RD,P,Fo,FP),Fo1).

is_exists(exists(D,Fo),exists(D1,Fo1),C) :-
   nonvar(D), D = [_|_],!,                        % nested exists
   unfold_nested_exists(exists(D,Fo),exists(DNew,FoNew)),
   is_foreach(foreach(DNew,[],FoNew,true),foreach(D1,_,Fo1,_),C).
is_exists(exists(D,Fo),exists(D1,Fo1),C) :-
   is_foreach(foreach(D,[],Fo,true),foreach(D1,_,Fo1,_),C).  

% TODO add support for nested nexists
is_nexists(nexists(D,Fo),nexists(D1,Fo1),C) :-
   nonvar(D), functor(D,A,_), A \== '[|]',!,
   is_foreach(foreach(D,[],Fo,true),foreach(D1,_,Fo1,_),C).

% exists([X in A,Y in B],Fo) --> exists(X in A,exists(X in B,Fo))
% exists([X in A,Y in B],[Z],Fo,FP) --> 
%   exists(X in A,[],exists(X in B,[Z],Fo,FP),true)
unfold_nested_exists(exists([D],Fo),exists(D,Fo)) :- !.
unfold_nested_exists(exists([D|RD],Fo),exists(D,Fo1)) :-
    unfold_nested_exists(exists(RD,Fo),Fo1).


%%%%%%%%%%%%%%%%%% let preprocessing

is_let(let(LVars,Conj,F),let(LVars,ConjNew,FNew),C) :-    
    term_variables(LVars,LVars1), LVars == LVars1,            % LVars: list of distinct variables
    %TODO - Conj: conjunction of functional predicates (use functional_pred)
    %TODO - check all variables in LVars are the result of exactly one functional predicate in Conj
    !,                         
    preproc_goal(Conj,ConjNew), 
    preproc(F,FNew,C).
is_let(let(_,_,_),_,_) :-
    msg_sort_error(let).

is_nlet(nlet(LVars,Conj,F),nlet(LVarsNew,ConjNew,FNew),C) :-  %controls for let and nlet are the same
    is_let(let(LVars,Conj,F),let(LVarsNew,ConjNew,FNew),C).

functional_pred(un(_X,_Y,Z),A) :- 
    var(Z), var(A), Z == A.
functional_pred(X is _E,A) :- 
    var(X), var(A), X == A.
%TO BE COMPLETED


%%%%%%%%%%%%%%%%%% cp preprocessing

cp_preproc(cp(A,B),cp(A,B),[set(A),set(B)]) :-
    var(A),var(B),!.
cp_preproc(cp(A,B),cp(A1,B1),Constrs) :-  %A=cp(_,_), B=cp(_,_)
    nonvar(A), A = cp(_,_),
    nonvar(B), B = cp(_,_),!,
    cp_preproc(A,A1,Constrs1),
    cp_preproc(B,B1,Constrs2),
    append(Constrs1,Constrs2,Constrs).
cp_preproc(cp(A,B),cp(A1,B1),Constrs) :-  %A=cp(_,_)
    nonvar(A), A = cp(_,_),!,
    cp_preproc(A,A1,Constrs1),
    preproc(B,B1,Constrs2),
    append(Constrs1,Constrs2,Constrs).
cp_preproc(cp(A,B),cp(A1,B1),Constrs) :-  %B=cp(_,_)
    nonvar(B), B = cp(_,_),!,
    preproc(A,A1,Constrs1),
    cp_preproc(B,B1,Constrs2),
    append(Constrs1,Constrs2,Constrs).
cp_preproc(cp(A,B),cp(A,B1),[set(A)|Constrs]) :-
    var(A),!,  %nonvar(B)
    (B = cp(_,_) ->
         cp_preproc(B,B1,Constrs)
    ;
         set_preproc(B,B1,Constrs)
    ).
cp_preproc(cp(A,B),cp(A1,B),[set(B)|Constrs]) :-
    var(B),!,  %nonvar(A)
    (A = cp(_,_) ->
         cp_preproc(A,A1,Constrs)
    ;
         set_preproc(A,A1,Constrs)
    ).
cp_preproc(cp(A,B),cp(A1,B1),Constrs) :-  %nonvar(A), nonvar(B)
    set_preproc(A,A1,Constrs1),!,
    (B = cp(_,_) ->
         cp_preproc(B,B1,Constrs2)
    ;
         set_preproc(B,B1,Constrs2)
    ),
    append(Constrs1,Constrs2,Constrs).
cp_preproc(cp(A,B),cp(A1,B1),Constrs) :-  %nonvar(A), nonvar(B)
    set_preproc(B,B1,Constrs2),!,
    (A = cp(_,_) ->
         cp_preproc(A,A1,Constrs1)
    ;
         set_preproc(A,A1,Constrs1)
    ),
    append(Constrs1,Constrs2,Constrs).
cp_preproc(_,_,_) :-
    msg_sort_error(cp).   

%%%%%%%%%%%%%%%%%% bag preprocessing

%bag_preproc({},{},[]) :-!.
%bag_preproc(X mwith A,X mwith B,[bag(X)|Constrs]) :-
%    var(X),!, preproc(A,B,Constrs).
%bag_preproc(X mwith A,Y with B,Constrs) :-
%    is_bag_ext(X),!,
%    preproc(A,B,Constrs1), preproc(X,Y,Constrs2),
%    append(Constrs1,Constrs2,Constrs).
%bag_preproc((*({}(A))),B,Constrs) :-
%    bag_preproc_elems(A,B,Constrs),!.
%bag_preproc(_,_,_) :-
%    msg_sort_error(bag),
%    fail.

%bag_preproc_elems(A, {} mwith A,[]) :-
%    var(A),!.
%bag_preproc_elems((A1,B1),B2 mwith A2,Constrs) :-
%    !,preproc(A1,A2,Constrs1),
%    bag_preproc_elems(B1,B2,Constrs2),
%    append(Constrs1,Constrs2,Constrs).
%bag_preproc_elems(M,MWT,Constrs) :-
%    aggr_comps_ext(M,_A,_X),!,
%    bag_preproc_bag(M,MWT,Constrs).
%bag_preproc_elems(A1,{} mwith A2,Constrs) :-
%    preproc(A1,A2,Constrs).

%bag_preproc_bag(M,X mwith B,[bag(X)|Constrs]) :-
%    aggr_comps_ext(M,A,X), var(X),!,
%    preproc(A,B,Constrs).
%bag_preproc_bag(M,Y mwith B,Constrs) :-!,
%    aggr_comps_ext(M,A,X), is_bag_ext(X),!,
%    preproc(A,B,Constrs1), preproc(X,Y,Constrs2),
%    append(Constrs1,Constrs2,Constrs).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% type constraints generation

%gen_type_constrs(_T1 in T2,C) :- !,
%    (other_aggrs(off),!,C=[set(T2)] ; C=[]).
%gen_type_constrs(_T1 nin T2,C) :- !,
%    (other_aggrs(off),!,C=[set(T2)] ; C=[]).
%
gen_type_constrs(_T1 in T2,SC) :- !,
     check_sorts([set(T2)],SC).
gen_type_constrs(_T1 nin T2,SC) :- !,
     check_sorts([set(T2)],SC).
gen_type_constrs(un(T1,T2,T3),SC) :- !,
     check_sorts([set(T1),set(T2),set(T3)],SC).
gen_type_constrs(nun(T1,T2,T3),SC) :- !,
     check_sorts([set(T1),set(T2),set(T3)],SC).
gen_type_constrs(disj(T1,T2),SC) :- !,
     check_sorts([set(T1),set(T2)],SC).
gen_type_constrs(ndisj(T1,T2),SC) :- !,
     check_sorts([set(T1),set(T2)],SC).
gen_type_constrs(subset(T1,T2),SC) :- !,
     check_sorts([set(T1),set(T2)],SC).
gen_type_constrs(ssubset(T1,T2),SC) :- !,
     check_sorts([set(T1),set(T2)],SC).
gen_type_constrs(inters(T1,T2,T3),SC) :- !,
     check_sorts([set(T1),set(T2),set(T3)],SC).
gen_type_constrs(diff(T1,T2,T3),SC) :- !,
     check_sorts([set(T1),set(T2),set(T3)],SC).
%
gen_type_constrs(size(T1,T2),SC) :- !,
     check_sorts([set(T1),integer(T2)],SC).
gen_type_constrs(sum(T1,T2),SC) :- !,
     check_sorts([set(T1),integer(T2)],SC).
gen_type_constrs(smin(T1,T2),SC) :- !,
     check_sorts([set(T1),integer(T2)],SC).
gen_type_constrs(smax(T1,T2),SC) :- !,
     check_sorts([set(T1),integer(T2)],SC).
%
gen_type_constrs(rel(T1),[]) :- !,      
     check_sorts([set(T1)],_).         
gen_type_constrs(dom(T1,T2),[rel(T1),set(T2)]) :- !,
     check_sorts([set(T1),set(T2)],_).
gen_type_constrs(ran(T1,T2),[rel(T1),set(T2)]) :- !,
     check_sorts([set(T1),set(T2)],_).
gen_type_constrs(comp(T1,T2,T3),[rel(T1),rel(T2),rel(T3)]) :- !,
     check_sorts([set(T1),set(T2),set(T3)],_).
gen_type_constrs(inv(T1,T2),[rel(T1),rel(T2)]) :- !,
     check_sorts([set(T1),set(T2)],_).
gen_type_constrs(id(T1,T2),[set(T1),rel(T2)]) :- !,
     check_sorts([set(T1),set(T2)],_).
%
gen_type_constrs(pfun(T1),[]) :- !,   
     check_sorts([set(T1)],_).
gen_type_constrs(dompf(T1,T2),[pfun(T1),set(T2)]) :- !,
     check_sorts([set(T1),set(T2)],_).
gen_type_constrs(comppf(T1,T2,T3),T_constrs) :-  !,
     check_sorts([set(T1),set(T2),set(T3)],_),
     %(nopfcheck ->   
     %   T_constrs = []
     %;
     %   T_constrs = [pfun(T1),pfun(T2),pfun(T3)]
     %).
     T_constrs = [pfun(T1),pfun(T2),pfun(T3)].
gen_type_constrs(drespf(T1,T2,T3),[set(T1),pfun(T2),pfun(T3)]) :- !,
     check_sorts([set(T1),set(T2),set(T3)],_).
%
gen_type_constrs(dres(T1,T2,T3),[set(T1),rel(T2),rel(T3)]) :- !,
     check_sorts([set(T1),set(T2),set(T3)],_).
gen_type_constrs(rres(T1,T2,T3),[rel(T1),set(T2),rel(T3)]) :- !,
     check_sorts([set(T1),set(T2),set(T3)],_).
gen_type_constrs(dares(T1,T2,T3),[set(T1),rel(T2),rel(T3)]) :- !,
     check_sorts([set(T1),set(T2),set(T3)],_).
gen_type_constrs(rares(T1,T2,T3),[rel(T1),set(T2),rel(T3)]) :- !,
     check_sorts([set(T1),set(T2),set(T3)],_).
gen_type_constrs(oplus(T1,T2,T3),[rel(T1),rel(T2),rel(T3)]) :- !,
     check_sorts([set(T1),set(T2),set(T3)],_).
%
gen_type_constrs(nrel(T1),[]) :- !,
     check_sorts([set(T1)],_).
gen_type_constrs(npfun(T1),[]) :- !,
     check_sorts([set(T1)],_).
gen_type_constrs(ndom(T1,T2),SC) :- !,
     check_sorts([set(T1),set(T2)],SC).
gen_type_constrs(nran(T1,T2),SC) :- !,
     check_sorts( [set(T1),set(T2)],SC).
gen_type_constrs(ninv(T1,T2),SC) :- !,
     check_sorts([set(T1),set(T2)],SC).
gen_type_constrs(ncomp(T1,T2,T3),SC) :- !,
     check_sorts([set(T1),set(T2),set(T3)],SC).
gen_type_constrs(nid(T1,T2),SC) :- !,
     check_sorts([set(T1),set(T2)],SC).
%
gen_type_constrs(ndres(T1,T2,T3),SC) :- !,
     check_sorts([set(T1),set(T2),set(T3)],SC).
gen_type_constrs(nrres(T1,T2,T3),SC) :- !,
     check_sorts([set(T1),set(T2),set(T3)],SC).
gen_type_constrs(ndares(T1,T2,T3),SC) :- !,
     check_sorts([set(T1),set(T2),set(T3)],SC).
gen_type_constrs(nrares(T1,T2,T3),SC) :- !,
     check_sorts([set(T1),set(T2),set(T3)],SC).
gen_type_constrs(nrimg(T1,T2,T3),SC) :- !,
     check_sorts([set(T1),set(T2),set(T3)],SC).
gen_type_constrs(noplus(T1,T2,T3),SC) :- !,
     check_sorts([set(T1),set(T2),set(T3)],SC).
gen_type_constrs(ndompf(T1,T2),SC) :- !,
     check_sorts([set(T1),set(T2)],SC).
%
gen_type_constrs(apply(T1,_,_),[]) :- !,   
     check_sorts([set(T1)],_).
gen_type_constrs(napply(T1,_,_),SC) :- !,
     check_sorts([set(T1)],SC).

check_sorts(SC_in,SC_out) :- 
      sat_step(SC_in,SC_out,_,f).      
%
%     (sat_step(SC_in,SC_out,_,f) -> true
%      ;
%      msg_sort_error(sort) 
%     ).

%%%%%%%%%%%%% auxiliary predicates for set/multiset preprocessing

is_set_ext(X) :- functor(X,{},_),!.
is_set_ext(_ with _).

%is_bag_ext({}) :-!.
%is_bag_ext(X) :- X = *A, functor(A,{},_), !.
%is_bag_ext(_ mwith _).

is_ris_ext(ris(_CE_Dom,_Fl)) :- !.
is_ris_ext(ris(_CE_Dom,_,_Fl)) :- !.
is_ris_ext(ris(_CE_Dom,_LVars,_Fl,_P)) :- !.
is_ris_ext(ris(_CE_Dom,_LVars,_Fl,_P,_PP)).

aggr_comps_ext((A \ R),A,R) :-!.       %for compatibility with previous releases
aggr_comps_ext((A / R),A,R).          

is_ker(T) :-
    nonvar(T), functor(T,F,N),
    (   F \== with ->
        true
    ;
        N \== 2
    ).

msg_sort_error(set) :-
        throw(setlog_excpt('wrong set term')).
msg_sort_error(int) :-
        throw(setlog_excpt('wrong interval term')).
%msg_sort_error(bag) :-
%        throw(setlog_excpt('wrong multiset term')).
msg_sort_error(cp) :-
        throw(setlog_excpt('wrong cp term')).
msg_sort_error(ris) :-
        throw(setlog_excpt('wrong ris term')).
msg_sort_error(foreach) :-                       
        throw(setlog_excpt('wrong control term')).
msg_sort_error(sort) :-  
        throw(setlog_excpt('wrong argument')).
msg_sort_error(let) :-
        throw(setlog_excpt('wrong let construct')).


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%   Intensional set preprocessing
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

sf_in_clause((H :- B),(H1 :- B1)) :-
    !,sf_in_literal(H,[H1|List1]),
    sf_in_goal(B,List2),
    append(List1,List2,List),
    list_to_conj(B1,List).
sf_in_clause(A,(H :- B)) :-
    sf_in_hliteral(A,[H|List]),
    list_to_conj(B,List).

sf_in_goal(A,[A]) :-
    var(A),!.
sf_in_goal(true,[]) :-!.
sf_in_goal(A & B,NewL) :-
    !, sf_in_literal(A,A1),
    sf_in_goal(B,B1),
    append(A1,B1,NewL).
sf_in_goal(A,NewL) :-
    !, sf_in_literal(A,NewL).

sf_in_literal(A,[A]) :-
    var(A),!.
sf_in_literal(A or B,[A1 or B1]) :-
    !, sf_in_goal(A,L1),
    sf_in_goal(B,L2),
    list_to_conj(A1,L1),
    list_to_conj(B1,L2).
sf_in_literal(prolog_call(A),[prolog_call(A)]) :-!.
sf_in_literal(naf A,[naf A1]) :-
    !, sf_in_goal(A,L1),
    list_to_conj(A1,L1).
sf_in_literal(cneg A,[cneg A1]) :-
    !, sf_in_goal(A,L1),
    list_to_conj(A1,L1).
sf_in_literal(call(A),[call(A1)]) :-
    !, sf_in_goal(A,L1),
    list_to_conj(A1,L1).
sf_in_literal(call(A,C),[call(A1,C)]) :-
    !, sf_in_goal(A,L1),
    list_to_conj(A1,L1).
sf_in_literal(solve(A),[solve(A1)]) :-
    !, sf_in_goal(A,L1),
    list_to_conj(A1,L1).
sf_in_literal(assert(Cl),[assert(Cl1)]) :-
    !, sf_in_clause(Cl,Cl1).
sf_in_literal((A)!,[(A1)!]) :-
    !, sf_in_goal(A,L1),
    list_to_conj(A1,L1).
sf_in_literal(delay(A,G),[delay(A1,G1)]) :-
    !, sf_in_goal(A,L1),
    sf_in_goal(G,L2),
    list_to_conj(A1,L1),
    list_to_conj(G1,L2).
sf_in_literal(forall(X in S,exists(V,A)),L) :-
    !, sf_find([S],[S1],L1),
    sf_in_goal(A,L2),
    list_to_conj(A1,L2),
    append(L1,[forall(X in S1,exists(V,A1))],L).
sf_in_literal(forall(X in S,A),L) :-
    !, sf_find([S],[S1],L1),
    sf_in_goal(A,L2),
    list_to_conj(A1,L2),
    append(L1,[forall(X in S1,A1)],L).

sf_in_literal(A,NewA) :-
    A =.. [Pname|Args],
    sf_find(Args,Args1,NewL),
    B =.. [Pname|Args1],
    append(NewL,[B],NewA).

sf_in_hliteral(A,[B|NewL]) :-
    A =.. [Pname|Args],
    sf_find(Args,Args1,NewL),
    B =.. [Pname|Args1].

sf_find([],[],[]).
sf_find([Int|R],[Var|S],List) :-
    is_sf(Int,X,G),!,
    extract_vars(G,Vars),
    remove_var(X,Vars,Finalvars),
    check_control_var1(Vars,Finalvars),
    sf_translate(Int,Var,L1,Finalvars),
    sf_find(R,S,L2),
    append(L1,L2,List).

sf_find([A|R],[B|S],List) :-
    nonvar(A),
    A =.. [Fname|Rest],
    Rest \== [],!,
    sf_find(Rest,Newrest,List1),
    B =.. [Fname|Newrest],
    sf_find(R,S,List2),
    append(List1,List2,List).
sf_find([A|R],[A|S],List) :-
    sf_find(R,S,List).

check_control_var1(Vars,Finalvars) :-
    Vars == Finalvars, !,
    throw(setlog_excpt('formula of a set former must contain the control variable')).
check_control_var1(_Vars,_Finalvars).

sf_translate(SF,Y,[Pred],Vars) :-
    (SF={X:exists(_Var,Goal)},! ; SF={X : Goal}),
    length([_|Vars],N),
    newpred(Aux,N,[115, 101, 116, 108, 111, 103, 83, 70, 95]),    % "setlogSF_"
    Aux=..[AuxName,Y|Vars],
    newpred(Aux1,N,[115, 101, 116, 108, 111, 103, 83, 70, 95]),
    Aux1 =.. [Aux1Name,X|Vars],
    Pred = sf_call(Y,Aux1Name,AuxName,Vars),
    tmp_switch_ctxt(OldCtxt),   
    setassert((Aux1 :- Goal)),
    setassert((Aux :- X nin Y & Aux1)),
    switch_ctxt(OldCtxt,_).     

is_sf(Int,X,Phi) :-
    nonvar(Int), Int = {SExpr},
    nonvar(SExpr), SExpr = (X : Phi), var(X), 
    check_control_var2(X).

check_control_var2(X) :-
    nonvar(X), !,
    throw(setlog_excpt('control variable in a set former must be a variable')).
check_control_var2(_X).


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%    R.U.Q. preprocessing  %%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

ruq_in_clause((H :- B),(H :- NewB)) :-
    ruq_in_goal(B,NewB),
    !.
ruq_in_clause(H,H).

ruq_in_goal(Goal,NewGoal) :-
    rewrite_goal(Goal,NewGoal).
    %DBG write('***NEW GOAL:***'), write(NewGoal), nl.   % only for debugging

rewrite_goal(G,NewG) :-
    filter_on,!,
    normalize(G,G1),
    ruq_in_goal(G1,G2,G1,infer_rules),
    ruq_in_goal(G2,NewG,G2,fail_rules).
rewrite_goal(G,NewG) :-
    ruq_in_goal(G,NewG,G,no).

ruq_in_goal(A,A,_,_) :-
    var(A),!.
ruq_in_goal(A & B,GExt,G,RR) :-
    !, ruq_in_goal(A,A1,G,RR), ruq_in_goal(B,B1,G,RR),
    conj_append(A1,B1,GExt).
ruq_in_goal((A or B),((A1) or (B1)),_,RR) :-
    !, ruq_in_goal(A,A1,A,RR), ruq_in_goal(B,B1,B,RR).

ruq_in_goal(prolog_call(A),prolog_call(A),_,_) :-!.
ruq_in_goal(naf A,naf(A1),_,RR) :-
    !, ruq_in_goal(A,A1,A,RR).
ruq_in_goal(cneg A,cneg(A1),_,RR) :-
    !, ruq_in_goal(A,A1,A,RR).
ruq_in_goal(call(A),call(A1),_,no) :-
    !, rewrite_goal(A,A1).
ruq_in_goal(call(A),call(A1),_,RR) :-
    !, ruq_in_goal(A,A1,A,RR).
ruq_in_goal(call(A,C),call(A1,C),_,RR) :-
    !, ruq_in_goal(A,A1,A,RR).
ruq_in_goal(solve(A),solve(A1),_,RR) :-
    !, ruq_in_goal(A,A1,A,RR).
ruq_in_goal((A)!,(A1)!,_,RR) :-
    !, ruq_in_goal(A,A1,A,RR).
ruq_in_goal(delay(A,G),delay(A1,G1),_,RR) :-
    !, ruq_in_goal(A,A1,A,RR),
    ruq_in_goal(G,G1,G,RR).

ruq_in_goal(forall(X in _S,_Y),_,_,_) :-
    nonvar(X),
    !,
    throw(setlog_excpt('control variable in a RUQ must be a variable')).
ruq_in_goal(forall(X in S,G),NewG,_,_) :-
    !,
    extract_vars(G,V),
    remove_var(X,V,Vars),
    check_control_var_RUQ(V,Vars),
    length(V,N),
    newpred(Gpred,N,[115, 101, 116, 108, 111, 103, 82, 85, 81, 95]),       %"setlogRUQ_"
    Gpred =.. [_,X|Vars],
    tmp_switch_ctxt(OldCtxt),
    (   G = exists(_Var,B) ->
        setassert((Gpred :- B))
    ;
        setassert((Gpred :- G))
    ),
    switch_ctxt(OldCtxt,_),
    functor(Gpred,F,N),
    NewG = ruq_call(S,F,Vars).

ruq_in_goal(true,true,_,_) :- !.
ruq_in_goal(A,NewG,G,RR) :-   % try to call filtering rules
    RR \== no,
    user_def_rules(A,NewG,G,RR),!.
ruq_in_goal(A,A,_,_).
    %% N.B. no check for 'forall(X in {...,t[X],...})'
    %% add 'occur_check(X,S)' to enforce it

check_control_var_RUQ(Vars,Finalvars) :-
    Vars == Finalvars, !,
    throw(setlog_excpt('formula of a RUQ must contain the control variable')).
check_control_var_RUQ(_Vars,_Finalvars).


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%% User-defined rewriting rules %%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%


normalize(Goal,NewGoal) :-
    ruq_in_goal(Goal,NewGoal1,Goal,replace_rules),
    (Goal == NewGoal1 ->
        NewGoal=NewGoal1
    ;   
        normalize(NewGoal1,NewGoal)
    ).

user_def_rules(A,NewC,G,replace_rules) :- !,
    replace_rule(_RuleName,C,C_Conds,D,D_Conds,AddC),
    check_atom(C,A,R),
    list_call(C_Conds),
    conj_member_strong(D,D_Conds,G,[]),
    apply_equiv(R,AddC,NewC).

user_def_rules(A,NewC,G,infer_rules) :- !,
    inference_rule(RuleName,C,C_Conds,D,D_Conds,E,AddC),
    check_atom(C,A,_R),
    list_call(C_Conds),
    conj_member_strong(D,D_Conds,G,E),
    trace_firules(RuleName),
    conj_append(AddC,A,NewC).

user_def_rules(A,NewC,G,fail_rules) :- !,
    fail_rule(RuleName,C,C_Conds,D,D_Conds,E),
    check_atom(C,A,_R),
    list_call(C_Conds),
    conj_member_strong(D,D_Conds,G,E),
    trace_ffrules(RuleName),
    conj_append((a = b),A,NewC).

conj_member_strong([],_,_,_) :- !.
conj_member_strong([T],D_Conds,G,E) :-
    conj_member_strong1(T,D_Conds,G,E),
    list_call(D_Conds),!.
conj_member_strong([T|R],D_Conds,G,E) :-
    R \== [],
    conj_member_strong1(T,D_Conds,G,E),
    conj_member_strong(R,D_Conds,G,E),!.

conj_member_strong1(T,_D_Conds,(A & _Cj),E) :-
    check_atom(T,A,_R),
    list_ex(E,T).
conj_member_strong1(T,D_Conds,(_Y & RCj),E) :-
    conj_member_strong1(T,D_Conds,RCj,E).

check_atom(T,A,no) :-
    A = T, !.
check_atom(T,A,RuleId) :-
    equiv_rule(RuleId,T,T1),!,
    A = T1.

list_call([]) :- !.
list_call([G|R]) :-
    call(G),
    list_call(R).

list_ex([],_).
list_ex([A|R],T) :-
    T \== A, list_ex(R,T).   % to exclude identical atoms

apply_equiv(no,A,A).
apply_equiv(R,A & B,A1 & B1) :-
    equiv_rule(R,A,A1),!,
    apply_equiv(R,B,B1).
apply_equiv(R,A & B,A & B1) :- !,
    apply_equiv(R,B,B1).
apply_equiv(R,A,A1) :-
    equiv_rule(R,A,A1),!.
apply_equiv(_R,A,A).


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% New predicate generation

newpred(P,A,T) :-
    nb_getval(newpred_counter,Y),       
    Z is Y + 1,
    nb_setval(newpred_counter,Z),     
    name(Y,Ylist),
    append(T,Ylist,Plist),
    name(Pred,Plist),
    mklist(L,A),
    P =.. [Pred|L].


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% transform_goal/2
% Transform a goal from the external representation to the
% internal representation, by rewriting intensional sets,
% RUQs, set and bag terms

transform_goal(Goal_external,Goal_internal) :-
    sf_in_goal(Goal_external,Goal_ruqL),
    list_to_conj(Goal_ruq,Goal_ruqL),
    preproc_goal(Goal_ruq,Goal),!,
    ruq_in_goal(Goal,Goal_internal).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% transform_clause/2
% Transform a clause from the external representation to the
% internal representation, by rewriting intensional sets,
% RUQs, set and bag terms

transform_clause(Clause_external,Clause_internal) :-
    sf_in_clause(Clause_external,ExplClause),
    preproc_clause(ExplClause,ExtClause),
    ruq_in_clause(ExtClause,Clause_internal).


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%     Postprocessing
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%%%%%%%%%%%%% Set (multiset) postprocessor:
%%%%%%%%%%%%% from 'with' ('mwith') to {...} (*({...})) notation
%%%%%%%%%%%%% from 'with' to {...} notation

postproc(X,X) :-
    var(X),!.
postproc(X,X) :-
    atomic(X),!.

postproc(int(A,B),{}) :-      % int(a,b), b < a --> {}
    integer(A), integer(B),
    B < A,!.
postproc(X,{}) :-     % cp({},_) or cp({},{}) --> {}
    cp_term(X,A,_B),     
    nonvar(A), is_empty(A),!.
postproc(X,{}) :-     % cp(_,{}) --> {}
    cp_term(X,_A,B),     
    nonvar(B), is_empty(B),!.
postproc(X,{}) :-
    ris_term(X,ris(CE_Dom,_V,_Fl,_P,_PP)),
    nonvar(CE_Dom), CE_Dom = (_CtrlExpr in Dom),
    nonvar(Dom), is_empty(Dom),!.
postproc(X,Z) :-
    ris_term(X,ris(CE_Dom,V,Fl,P,PP)),!,
    remove_type_constraints(PP,PPRed),
    =..(ris(CE_Dom,V,Fl,P,PPRed),[F|ListX]),
    postproc_all(ListX,ListZ),
    =..(Z,[F|ListZ]).
postproc(X,Y) :-
    nonvar(X), X = _ with _,!,
    norep_in_set(X,X1),
    with_postproc(X1,Y).
%postproc(X,Y) :-
%    nonvar(X), X = _ mwith _,!,
%    mwith_postproc(X,Z),
%    mwith_out(Z,Y).
postproc(X,Z) :-
    nonvar(X),
    =..(X,[F|ListX]),
    postproc_all(ListX,ListZ),
    =..(Z,[F|ListZ]).

postproc_all([],[]).
postproc_all([A|L1],[B|L2]) :-
    postproc(A,B),
    postproc_all(L1,L2).

remove_type_constraints(true,true) :- !.
remove_type_constraints((C1 & C2),CR) :-
    type_constr(C1),!,
    remove_type_constraints(C2,CR).
remove_type_constraints((C1 & C2),(C1 & CR)) :- !,
    remove_type_constraints(C2,CR).
remove_type_constraints(C,CR) :-
    remove_type_constraints((C & true),CR).


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% set postprocessing

with_postproc(A,A) :-
    var(A),!.
with_postproc(K,KExt) :-
    is_ker(K), !,
    postproc(K,KExt).
with_postproc(A,{}(B)) :-
    postproc_list(A,B).

postproc_list(X with A1,(A2 / X)) :-
    var(X),
    !,
    postproc(A1,A2).
postproc_list({} with A1,A2) :- !,
    postproc(A1,A2).
postproc_list(K with A1,Res) :-       % evaluating trivial RIS
    ris_term(K,ris(CE_Dom,_V,_Fl,_P,_PP)),
    nonvar(CE_Dom), CE_Dom = (_CtrlExpr in Dom),
    ground(Dom), !,
    final_sat([B1 is K],_),
    postproc(A1,A2),
    (   B1=={} ->
        Res=A2
    ;
        postproc_list(B1,B2),Res=(A2,B2)
    ).
postproc_list(K with A1,Res) :-
    is_ker(K),!,
    postproc(K,KExt), postproc(A1,A2),
    (   KExt=={} ->
        Res=A2
    ;
        Res=(A2 / KExt)
    ).
postproc_list(B1 with A1,(A2,B2)) :-
    postproc(A1,A2),postproc_list(B1,B2).


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% bag postprocessing

%mwith_out({}(X),*({}(X))).

%mwith_postproc(A,A) :- var(A),!.
%mwith_postproc({},{}) :- !.
%mwith_postproc(A,{}(B)) :-
%    bag_postproc_list(A,B).

%%bag_postproc_list(X mwith A1,(A2 \ X)) :-
%bag_postproc_list(X mwith A1,(A2 / X)) :-
%    var(X),!,postproc(A1,A2).
%bag_postproc_list({} mwith A, A) :-
%    var(A),!.
%bag_postproc_list({} mwith A1,A2) :-!,
%    postproc(A1,A2).
%bag_postproc_list(B1 mwith A1,(A2,B2)) :-
%    postproc(A1,A2), bag_postproc_list(B1,B2).


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%                              %%%%%%%%%%%%%%%%%
%%%%%%%%%     General auxiliary predicates     %%%%%%%%%%%%%%
%%%%%%%%%%%%%%                              %%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%%%%%%%%%%%%%%%%%%%%% Exported predicates:
%
% List manipulation
%             mklist/2,
%             memberrest/3,
%             memberall/4,
%             member_strong/2,
%             not_in/2,
%             listunion/3,
%             subset_strong/2,
%             norep_in_list/2,
% Conjunction manipulation
%             list_to_conj/2,
%             conj_append/3,
% Set manipulation
%             set_term/1,
%             with_term/1,
%             bounded/1
%             split/3,
%             norep_in_set/2,
%             set_length/2,
%             set_member_strong/2,
%%             set_member_rest/4,
%             list_to_set/3,
%             mk_set/2,
%             mk_test_set/3,
%             rel_term/1,
%             pfun_term/1,
% List/Set/Bag/Interval/RIS/CP manipulation
%             aggr_term/1,
%             tail/2,
%             tail2/2,
%             same_tail/3,
%             replace_tail/3,
%             replace_tail2/3,
%             empty_aggr/1,
%             is_empty/1,
%             nonvar_is_empty/1,
%             var_or_empty/1,
%             unify_empty/2,
%             set_int/1,
%             aggr_comps/3,
%             first_rest/4,
%             var_st/1,
%             var_ris_st/1,
%             var_ris_st/2,
% Interval manipulation
%             int_term/1,
%             int_term/3,
%             closed_intv/3,
%             open_intv/1,
%             nonopen_intv/1,
%             int_to_set/2,
%             int_length/2,
% Bag manipulation
%%             bag_term/1,
%%             bag_tail/2,
%%             de_tail/2,
%Variable manipulation
%             samevar/2,
%             samevar/3,
%             samevar3/3,
%             one_var/2,
%             chvar/6,
%             chvar/7,
%             find_corr/4,
%             occurs/2,
%             occur_check/2
%             extract_vars/2,
%             findallvars/3,
%             remove_var/3,
%             remove_list/3,
%             alldist/1,
%             not_in_vars/2,
% Arithmetic expressions manipulation
%             simple_integer_expr/1,
%             simple_arithm_expr/1,
%             arithm_expr/1,
%             integer_expr/1,
%             arithm_expr_error_msg/1,
%             test_integer_expr/1


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%     List manipulation
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

vars_list(L) :-
    nonvar(L), L = [], !.
vars_list(L) :-
    nonvar(L), L = [V|R], 
    var(V),
    vars_list(R).

mklist([],0) :- !.
mklist([_|R],N) :-
    M is N-1,
    mklist(R,M).

%member(X,[X|_R]).
%member(X,[_|R]) :-member(X,R).

memberrest(X,[X|R],R) :- !.
memberrest(X,[_|R],L) :-
    memberrest(X,R,L).

memberall(A,B,[A|_R],[B|_S]).
memberall(A,B,[_|R],[_|S]) :-
    memberall(A,B,R,S).

%append([],L,L).
%append([X|L1],L2,[X|L3]) :-
%   append(L1,L2,L3).

member_strong(A,[B|_R]) :-
    A == B, !.
member_strong(A,[_|R]) :-
    member_strong(A,R).

notin(_,[]).       % not member strong
notin(A,[B|R]) :-
    A \== B, notin(A,R).

listunion([],L,L).
listunion([A|R],X,[A|S]) :-
    notin(A,X),!,
    listunion(R,X,S).
listunion([_A|R],X,S) :-
    listunion(R,X,S).

subset_strong([],_L) :-!.
subset_strong([X|L1],L2) :-
    member_strong(X,L2),
    subset_strong(L1,L2).

norep_in_list([],[]) :-!.
norep_in_list([A|R],S) :-
    member_strong(A,R),!,
    norep_in_list(R,S).
norep_in_list([A|R],[A|S]) :-
    norep_in_list(R,S).


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%     Set manipulation
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

set_term(T) :-
    nonvar(T),
    (   T = {} ->
        true
    ;
        T = _ with _
    ).

with_term(T) :-        % not used
    nonvar(T), T=_ with _.

bounded(T) :-
    var(T),!,fail.
bounded({}) :- !.
bounded(R with _) :-
    bounded(R).

%%%% split(S,N,L) true if S is a set term of the form N with tn with ... with t1
%%%% (n >= 0) and L is the list [t1,...,tn]
split(N,N,[]) :-
    var(N),!.
split(S with T, N, [T|R]) :-
    split(S,N,R).

norep_in_set(X,X) :- var(X),!.
norep_in_set(K,K) :- is_ker(K), !.
norep_in_set(R with A,S) :-
    set_member_strong(A,R),!,
    norep_in_set(R,S).
norep_in_set(R with A,S with A) :-
    norep_in_set(R,S).

set_length(S,N) :-
    set_length(S,0,N).

set_length(X,_,_) :-
    var(X),
    !,
    fail.
set_length(S,N,N) :-
    is_empty(S),
    !.
set_length(int(A,B),N,M) :-
    !,
    M is N + (B - A) + 1.
set_length(R with _X,N,M) :-
    N1 is N + 1,
    set_length(R,N1,M).

set_member_strong(A,B) :-
    nonvar(B),
    B = _ with X,
    A == X,
    !.
set_member_strong(A,B) :-
    nonvar(B),
    B = Y with _,
    set_member_strong(A,Y).

%set_member_rest(_X,R,_C,_R) :-    % not used
%       var(R), !, fail.
%set_member_rest(X,R with Y,C,R) :-
%       sunify(X,Y,C).
%set_member_rest(X,R with Y,C,RR with Y) :-
%       set_member_rest(X,R,C,RR).

list_to_set(L,S,[]) :-            % list_to_set(+list,?set,-constraint)
    var(S),!,
    mk_set(L,S).
list_to_set(L,S,C) :-
    mk_test_set(L,S,C).

mk_set([], {}).
mk_set([X|L], R with X) :-
    mk_set(L, R).

mk_test_set([], {}, []).
mk_test_set([X|L], S, Cout) :-
    sunify(S, R with X, C1),
    list_to_set(L, R, C2),
    append(C1, C2, Cout).

rel_term(X) :- 
    var(X),!.
rel_term(X) :- 
    nonvar(X),is_empty(X),!.
rel_term(S with [_,_]) :- !,   
    rel_term(S).
rel_term(X) :-                     
    ris_term(X,ris(_,_,_,[_A1,_A2],_)),!.
rel_term(X) :-                     
    X = cp(_A,_B),!.

pfun_term(X) :-
    var(X),!.
pfun_term(X) :- 
    nonvar(X),is_empty(X),!.
pfun_term(PFun with P) :-
    pfun_term_cont(PFun,P),
    pfun_term(PFun).

pfun_term_cont({},_P1) :- !.
pfun_term_cont(F1 with P2,P1) :-
    nofork(P1,P2),
    pfun_term_cont(F1,P1).

nofork([X1,_Y1],[X2,_Y2]) :-
    X1 \== X2,!.
nofork([X1,Y1],[X2,Y2]) :-
    X1 = X2, Y1 = Y2.


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%     Interval manipulation
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

int_term(T) :-
    nonvar(T), T = int(_,_).

int_term(T,A,B) :-                  
    nonvar(T), T = int(A,B).

closed_intv(T,A,B) :-                % closed_intv(I,A,B) is true if I is a term that
    nonvar(T),                       % denotes the closed interval int(A,B)
    T = int(A,B),
    integer(A), integer(B),!.

open_intv(S) :-
    nonvar(S), S = int(A,B),
    (   var(A)  ->
        true
    ;
        var(B)
    ).

nonopen_intv(S) :-
    open_intv(S),!,
    throw(setlog_excpt('interval bounds are not sufficiently instantiated')).
nonopen_intv(_S).

int_to_set(int(A,A),{} with A) :- !. % int_to_set(+I,?S) is true if S denotes the set
int_to_set(int(A,B),S with A) :-     % of all elements of the interval I
    A < B,
    A1 is A + 1,
    int_to_set(int(A1,B),S).

int_to_set(int(A,A),R with A,R) :- !.% int_to_set(+I,?S) is true if S contains the set
int_to_set(int(A,B),S with A,R) :-   % of all elements of the interval I
    A < B,
    A1 is A + 1,
    int_to_set(int(A1,B),S,R).

int_length(int(A,B),L) :-
    N is B - A + 1,
    (   N < 0 ->
        L = 0
    ;
        L = N
    ).


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%     Bag manipulation
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%bag_term(T) :-
%    nonvar(T),
%    (   T={} ->
%        true
%    ;
%        T = _ mwith _
%    ).

%bag_tail(R mwith _ ,R) :- var(R),!.
%bag_tail({} mwith _ ,{}) :- !.
%bag_tail(R mwith _ ,T) :-
%    bag_tail(R,T).

%de_tail(R,{}) :- var(R),!.
%de_tail({},{}) :- !.
%de_tail(R mwith S,K mwith S) :-
%    de_tail(R,K).


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%   List/Set/Bag/Interval/RIS/CP manipulation
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

aggr_term(S) :- set_term(S), !.
aggr_term(S) :- int_term(S), !.
aggr_term(S) :- ris_term(S), !.
aggr_term(S) :- cp_term(S).

tail(R,R) :- var(R),!.                   %attn. tail({},T), tail(int(a,b),T), tail(cp(...),T) --> false
tail(R with _,R) :- var(R),!.            %tail(ris(X in D,...),T) ---> T=tail(D)
tail(R,RR) :-
    ris_term(R,ris(_ in D,_,_,_,_)),!,   %ris: returns the tail of the RIS domain
    tail(D,RR).
tail({} with _,{}) :- !.
tail(int(_A,_B) with _,{}) :- !.
tail(R  with _,RR) :-
    ris_term(R,ris(_ in D,_,_,_,_)),!,
    (tail(D,RR),! ; RR={}).
tail(R with _,R) :-
    R = cp(_,_),!.
tail(R with _,T) :- !,
    tail(R,T).

tail2(R,R) :- var(R),!.
tail2(R with _,R) :- var(R),!.
tail2({} with _,{}) :- !.
tail2(int(_A,_B) with _,{}) :- !.
tail2(R with _,RR) :-
    ris_term(R,RR),!.                     %ris: returns the RIS itself
tail2(R with _,R) :-
    R = cp(_,_),!.                        %cp: returns the CP itself
tail2(R with _,T) :- !,
    tail2(R,T).

same_tail(A,B,X) :-
    (   tail(A,TA),samevar(X,TA) ->
        true
    ;
        tail(B,TB),samevar(X,TB)
    ).

replace_tail(R,N,N) :- var(R),!.
replace_tail({},N,N) :- !.
replace_tail(R,N,ris(X in Dnew,V,F,P,PP)) :-   % replace_tail( {t1,...,tn/{x : D|F @P}}, N)
    ris_term(R,ris(X in D,V,F,P,PP)),!,        % ---> {t1,...,tn/{x : N|F @P}}
    %%%%X==P,!,
    replace_tail(D,N,Dnew).
replace_tail(R,N,N) :-
    R = cp(_,_),!.
replace_tail(R1 with X,N,R2 with X) :-
    replace_tail(R1,N,R2).

replace_tail2(R,N,N) :- var(R),!.
replace_tail2({},N,N) :- !.
replace_tail2(R,N,N) :-                        % replace_tail2( {t1,...,tn/{x : D|F @P}}, N)
    ris_term(R),!.                             % ---> {t1,...,tn/N}
replace_tail2(R,N,N) :-
    R = cp(_,_),!.
replace_tail2(R1 with X,N,R2 with X) :-
    replace_tail2(R1,N,R2).

empty_aggr(A) :-                  % empty set/multiset/list
    (is_empty(A),! ; A == []).

is_empty({}) :- !.                % empty set (requires nonvar(S))
is_empty(S) :-
    closed_intv(S,L,H),
    L > H,!.
is_empty(S) :-
    ris_term(S,ris(_ in Dom,_,_,_,_)),
    nonvar(Dom), is_empty(Dom),!.
is_empty(cp(A,B)) :-
    (nonvar(A),is_empty(A),! ; nonvar(B),is_empty(B)).

nonvar_is_empty(S) :-
    nonvar(S), is_empty(S).

var_or_empty(T) :-
    var_st(T),!.
var_or_empty(T) :-
    is_empty(T).

unify_empty(S,[]) :-
    var(S), !, S = {}.
unify_empty({},[]) :- !.
unify_empty(S,[L > H]) :-
    S = int(L,H),!.
unify_empty(S,[S = {}]) :-
    ris_term(S),!.
unify_empty(S,C) :-
    S = cp(A,B),
    (   unify_empty(A,C)
    ;   unify_empty(B,C)
    ).

set_int(_ with _) :-!.      %set(S): true if S is either an extensional set or an interval or a CP
set_int(int(_,_)) :- !.
set_int(cp(_,_)).

aggr_comps(S,X,R) :-
%    other_aggrs(off),
    !,
    S = R with X.
aggr_comps(R with X,X,R) :- !.    % set
%aggr_comps(R mwith X,X,R) :- !.   % bag
aggr_comps([X | R],X,R).          % list

%first_rest(+S,?X,-R,-C)
first_rest(R with X,X,R,[]) :- !.   % first_rest(S,X,R,C): true if: S is a not-empty set (interval, RIS, CP)
first_rest(int(X,B),X,R,[]) :-      % R is S without its first component and
    integer(X), integer(B),         % X is the first component of S and C is the list of computed constraints
    X < B,
    !,
    X1 is X + 1,
    R = int(X1,B).
first_rest(int(X,B),X,{},[]) :-
    integer(X), integer(B),
    X = B,
    !.
first_rest(RIS,A,R,C) :-
    ris_term(RIS,RISe), !,
    final_sat([RISe = R with A, A nin R, set(R)],C),!.
first_rest(cp(X,Y),A,R,C) :- !,
    final_sat([cp(X,Y) = R with A, A nin R, set(R)],C),!.

var_st(X) :-                        % true if X is a variable or a variable cp-term 
    var(X),
    !.
var_st(X) :-
    X = cp(X1,X2),
    (var_st(X1) ->
        true
    ;
        var_st(X2)
    ).

var_ris_st(X) :-                    % true if X is a variable or a variable-RIS or a variable-CP 
    var(X),!.
var_ris_st(X) :-     
    ris_term(X,ris(_ in Dom,_,_,_,_)),
    open_intv(Dom),!.   
var_ris_st(X) :-
    ris_term(X,ris(_ in Dom,_,_,_,_)),!,
    var_ris(Dom).
var_ris_st(X) :-
    X = cp(X1,X2),
    (var_st(X1) ->
        true
    ;
        var_st(X2)
    ).

var_ris_st(X,X) :-                 % var_ris_st(X,Y): true if X is a variable and Y is X itself 
    var(X),!.                      % or X is a variable-RIS and Y is the RIS domain
var_ris_st(X,Dom) :-               % or X is a variable-CP and Y is any of its variable component
    ris_term(X,ris(_ in Dom,_,_,_,_)),
    open_intv(Dom),!.   
var_ris_st(X,Dom) :-
    ris_term(X,ris(_ in Dom,_,_,_,_)),!,
    var_ris(Dom).
var_ris_st(X,X1) :-
    X = cp(X1,_X2),
    var_st(X1).
var_ris_st(X,X2) :-
    X = cp(_X1,X2),
    var_st(X2).


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%  Arithmetic expressions manipulation
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

simple_integer_expr(E) :-  % true if E is a var or an integer constant; otherwise fail
    (   var(E) ->
        true
    ;
        integer(E)
    ).

simple_arithm_expr(E) :-  % true if E is a var or a numeric constant; otherwise fail
    (   var(E) ->
        true
    ;
        number(E)
    ).

arithm_expr(E) :-        % true if E is a ground arithmetic expression; otherwise throw setlog_excpt
    catch(_X is E,Msg,arithm_expr_error_msg(Msg)).

integer_expr(E) :-       % true if E is an integer expression; otherwise throw setlog_excpt
    int_solver(clpfd),!,
    catch(fd_expr(_X,E),Msg,arithm_expr_error_msg(Msg)).
integer_expr(E) :-
    catch(q_expr(_X,E),Msg,arithm_expr_error_msg(Msg)).

arithm_expr_error_msg(_Text) :-
    throw(setlog_excpt('problem in arithmetic expression')).

test_integer_expr(E) :-    % true if E is an integer expression; otherwise fail
    int_solver(clpfd),!,
    catch(fd_expr(_X,E),_Error,fail).
test_integer_expr(E) :-
    catch(q_expr(_X,E),_Error,fail).


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%  Variable manipulation
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

samevar(X,Y) :-
    var(X), var(Y), X == Y.

samevar(X,Y,Z) :-           %true if X is identical to either Y or Z
    (samevar(X,Y),! ; samevar(X,Z)).

samevar3(X,Y,Z) :-          %true if either X==Y or X==Z or Y==Z
    (samevar(X,Y),! ; samevar(X,Z),! ; samevar(Y,Z)).

one_var(X,Y) :-
    (var(X),! ;  var(Y)).

chvar(L1,[X|L1],X,L2,[Y|L2],Y) :-                %chvar(+L1,-LVars,+Term,+L1New,-LVarsNew,-TermNew)
    var(X), notin(X,L1), !.                      %e.g. chvar([Y],V1,f(X,Y,Z),[W],V2,T2)
chvar(L1,L1,X,L2,L2,Y) :-                        %--> V1 = [Z,X,Y], V2 = [_N1,_N2,W], T2 = f(_N1,W,_N2)
    var(X), find_corr(X,Y,L1,L2),!.
chvar(L1,L1new,(H :- B),L2,L2new,(H1 :- B1)) :-
    !, chvar(L1,L1a,H,L2,L2a,H1),
    chvar(L1a,L1new,B,L2a,L2new,B1).
chvar(L1,L1new,(B1 & B2),L2,L2new,(B1a & B2a)) :-
    !, chvar(L1,L1a,B1,L2,L2a,B1a),
    chvar(L1a,L1new,B2,L2a,L2new,B2a).
chvar(L1,L1,F,L2,L2,F) :-
    atomic(F),!.
chvar(L1,L1new,F,L2,L2new,F1) :-
    F =.. [Fname|Args],
    chvar_all(L1,L1new,Args,L2,L2new,Brgs),
    F1 =.. [Fname|Brgs].

chvar_all(L1,L1,[],L2,L2,[]) :-!.
chvar_all(L1,L1b,[A|R],L2,L2b,[B|S]) :-
    chvar(L1,L1a,A,L2,L2a,B),
    chvar_all(L1a,L1b,R,L2a,L2b,S).

chvar(V,L1,L1,X,L2,L2,X) :-   %chvar(+LocalVars,+InitialVars,-FinalVars,+Term,+InitialNewVars,-FinalNewVars,-NewTerm):
    var(X), notin(X,V), !.    %same as chvar/6 but it replaces only variables which occur in the list 'LocalVars'
chvar(_,L1,[X|L1],X,L2,[Y|L2],Y) :-       %e.g. chvar([X,Y],[],V1,f(X,g(Y,Z),Z,X),[],V2,T2) -->
    var(X), notin(X,L1), !.               %V1 = [Y,X], V2 = [_N2,_N1], T2 = f(X',g(_N2,Z),Z,_N1)
chvar(_,L1,L1,X,L2,L2,Y) :-
    var(X), find_corr(X,Y,L1,L2),!.
chvar(_,L1,L1,F,L2,L2,F) :-
    atomic(F),!.
chvar(V,L1,L1new,F,L2,L2new,F1) :-
    F =.. [Fname|Args],
    chvar_all(V,L1,L1new,Args,L2,L2new,Brgs),
    F1 =.. [Fname|Brgs].

chvar_all(_,L1,L1,[],L2,L2,[]) :-!.        %same as chvar_all/6 but using chvar/7 with the first argument
chvar_all(V,L1,L1b,[A|R],L2,L2b,[B|S]) :-  %representing LocalVars
    chvar(V,L1,L1a,A,L2,L2a,B),
    chvar_all(V,L1a,L1b,R,L2a,L2b,S).

%ex. find_corr(X,Y,[V,X,W],[A,B,C]) --> Y=B
%ex. find_corr(H,Y,[V,X,W],[A,B,C]) --> false
find_corr(X,Y,[A|_R],[Y|_S]) :-
    X == A,
    !.
find_corr(X,Y,[_|R],[_|S]) :-
    find_corr(X,Y,R,S).

occurs(_X,T) :-   % occur(X,T): true if variable X occurs in term T
    ground(T),
    !,
    fail.
occurs(X,Y) :-
    var(Y),
    samevar(X,Y),
    !.
occurs(_X,Y) :-   % occurs(X,T): false if T is a RIS
    ris_term(Y),
    !,
    fail.
occurs(X,Y) :-
    nonvar(Y),
    Y =.. [_|R],
    occur_list(X,R).

occur_list(_X,[]) :-
    !,
    fail.
occur_list(X,[A|_R]) :-
    occurs(X,A),
    !.
occur_list(X,[_|R]) :-
    occur_list(X,R).

occur_check(_X,_Y) :-    % occur_check(X,T): true if variable X DOES NOT occur in term T
    occur_check(off),
    !.
occur_check(_X,T) :-
    ground(T),
    !.
occur_check(X,Y) :-
    var(Y),
    !,
    X \== Y.
occur_check(X,R with T) :-
    ris_term(R),
    !,
    occur_check(X,T).
occur_check(X,Y) :-
    Y =.. [_|R],
    occur_check_list(X,R).

occur_check_list(_X,[]) :-
    !.
occur_check_list(X,[A|R]) :-
    occur_check(X,A),
    occur_check_list(X,R).

% extract_vars(T,L): true if L is the list of all "non-local" variables in term T
extract_vars(A,[A]) :-
    var(A),
    !.
%RIS
extract_vars(Ris,Vars) :-                  % ris/2, ris/3, ris/4, ris/5
    is_ris(Ris,ris(CT in D,V,F,P,_PP)),!,      
    extract_vars(CT,L1),
    listunion(L1,V,LocalV),
    extract_vars(F,L2),
    extract_vars(P,L3),
    listunion(L2,L3,L23),
    extract_vars(D,L4),
    listunion(L23,L4,L),
    remove_list(LocalV,L,Vars).
%exits/nexists  
extract_vars(exists(V,B),Vars) :-         % exists(Var,F)
    var(V),!,
    extract_vars(B,List),
    remove_var(V,List,Vars).
extract_vars(exists(V,B),Vars) :-         % exists(VarList,F)
    vars_list(V),!, 
    extract_vars(B,List),
    remove_list(V,List,Vars).
extract_vars(exists(D,F),Vars) :- !,      % exists(X in D,F)
    extract_vars(exists(D,[],F,true),Vars).
extract_vars(exists(CT in D,V,F,P),Vars) :- !,
    extract_vars(CT,L1),                  % exists(X in D,LocalVars,F,P)
    listunion(L1,V,LocalV),
    extract_vars(F,L2),
    extract_vars(P,L3),
    listunion(L2,L3,L23),
    extract_vars(D,L4),
    listunion(L23,L4,L),
    remove_list(LocalV,L,Vars).
extract_vars(exists(LDom,V,F,P),Vars) :- % exists([X1 in A1,...,Xn in An],...)
    extract_vars_list(LDom,L1),!,                
    listunion(L1,V,LocalV),
    extract_vars(F,L2),
    extract_vars(P,L3),
    listunion(L2,L3,L),
    remove_list(LocalV,L,Vars).
extract_vars(nexists(V,B),Vars) :-       % nexists(Var,F) 
    var(V),!,
    extract_vars(exists(V,B),Vars).
extract_vars(nexists(CT in D,F),Vars) :- !,      % nexists(X in D,LocalVars,F,P) 
    extract_vars(exists(CT in D,[],F,true),Vars).
extract_vars(nexists(CT in D,V,F,P),Vars) :- !,  % nexists(X in D,LocalVars,F,P)
    extract_vars(exists(CT in D,V,F,P),Vars).
%forall
extract_vars(forall(X in Y,B),Vars) :-!,
    extract_vars(Y,L1),
    extract_vars(B,L2),
    listunion(L1,L2,L),
    remove_var(X,L,Vars).
%foreach
extract_vars(foreach(CT in D,F),Vars) :- !,     % foreach(X in D,F) 
    extract_vars(foreach(CT in D,[],F,true),Vars).
extract_vars(foreach(CT in D,V,F,P),Vars) :- !, % foreach(X in D,LocalVars,F,P) 
    extract_vars(CT,L1),
    listunion(L1,V,LocalV),
    extract_vars(F,L2),
    extract_vars(P,L3),
    listunion(L2,L3,L23),
    extract_vars(D,L4),
    listunion(L23,L4,L),
    remove_list(LocalV,L,Vars).
extract_vars(foreach(LDom,F),Vars) :-           % foreach([X1 in A1,...,Xn in An],F)
    nonvar(LDom), LDom = [_|_],!,
    extract_vars(foreach(LDom,[],F,true),Vars).
extract_vars(foreach(LDom,V,F,P),Vars) :-       % foreach([X1 in A1,...,Xn in An],...)
    extract_vars_list(LDom,L1),!,               
    listunion(L1,V,LocalV),
    extract_vars(F,L2),
    extract_vars(P,L3),
    listunion(L2,L3,L),
    remove_list(LocalV,L,Vars).
extract_vars(nforeach(CT in D,F),Vars) :- !,    % nforeach(X in D,F)
    extract_vars(foreach(CT in D,[],F,true),Vars).
extract_vars(nforeach(CT in D,V,F,P),Vars) :- !,% foreach(X in D,LocalVars,F,P)
    extract_vars(foreach(CT in D,V,F,P),Vars).
%let/nlet
extract_vars(let(V,Conj,F),Vars) :- !,          % let(V,Conj,F)
    extract_vars(Conj,L1),
    extract_vars(F,L2),
    listunion(L1,L2,L),
    remove_list(V,L,Vars).
extract_vars(nlet(V,Conj,F),Vars) :- !,         % nlet(V,Conj,F)
    extract_vars(let(V,Conj,F),Vars).
%set former
extract_vars(Int,Vars) :-                       % {X : F}
    is_sf(Int,X,G),!,
    extract_vars(G,Vars1),
    remove_var(X,Vars1,Vars).
%all other terms
extract_vars(P,Vars) :-
    functor(P,_,A),!,
    findallvars(P,A,Vars).

extract_vars_list([],[]).         
extract_vars_list([CT in _D|DVars],LocalV) :-
    extract_vars(CT,L1),
    extract_vars_list(DVars,L2),
    listunion(L1,L2,LocalV).

findallvars(_P,0,[]) :- !.
findallvars(P,A,Vars) :-
    arg(A,P,Arg),
    extract_vars(Arg,L1),
    B is A-1,
    findallvars(P,B,L2),
    listunion(L1,L2,Vars).

remove_var(_,[],[]).
remove_var(X,[Y|L],S) :-
    X == Y,
    !,
    remove_var(X,L,S).
remove_var(X,[Y|L],[Y|S]) :-
    remove_var(X,L,S).

remove_list([],L,L).
remove_list([X|R],Vars,Finalvars) :-
    remove_var(X,Vars,S),
    remove_list(R,S,Finalvars).

alldist([]).
alldist([A|R]) :-
    var(A), not_in_vars(A,R),
    alldist(R).

not_in_vars(_X,[]).
not_in_vars(X,[A|R]) :-
    X \== A, not_in_vars(X,R).


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%  Conjunction manipulation
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

list_to_conj(A & B,[A|R]) :-
    !,list_to_conj(B,R).
list_to_conj(true,[]) :-!.
list_to_conj(A,[A]).

conj_append(Cj1,Cj2,(Cj1 & Cj2)) :-
    var(Cj1),!.
conj_append(true,Cj2,Cj2) :- !.
conj_append((X & _Cj1),_Cj2,false) :-
    nonvar(X), X==false, !.
conj_append((X & Cj1),Cj2,Cj3) :-
    nonvar(X), X==true, !,
    conj_append(Cj1,Cj2,Cj3).
conj_append((X & Cj1),Cj2,(X & Cj3)) :- !,
    conj_append(Cj1,Cj2,Cj3).
conj_append(X,Cj2,(X & Cj2)).


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%% Configuration parameters %%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%%%%%%%%%% file names

%%% prefix for path names (default: '')
path('').

%%% filtering rules library file (default: 'setlog_rules.pl')
rw_rules('setlog_rules.pl').

%%% advanced size solver file (default: 'size_solver.pl')
size_solver_file('size_solver.pl').

%%% type-checker file (default: 'setlog_tc.pl')
type_checker_file('setlog_tc.pl').    

%%% verification condition generator (vcg) file (default: 'setlog_vcg.pl')
vcg_file('setlog_vcg.pl').

%%%%%%%%%% constraint solving strategies

%%% constraint solvers for integer expressions (default: clpfd)
%default_int_solver(clpfd).        % clp(FD) constraint solver
default_int_solver(clpq).          % clp(Q) constraint solver

%%% constraint solving mode (default: prover([]))    
%default_mode(solver).            % always compute variable substitutions
default_mode(prover(S)) :-	  % don't compute variable substitutions in not necessary    
   default_prover_mode_strategies(S). 
                                                	   
default_prover_mode_strategies([]).	

prover_mode_strategies([]) :- !.  % [X|L] is a subset of all possible prover mode strategies
prover_mode_strategies([X|L]) :-  
   all_prover_mode_strategies(All),
   subset([X|L],All).

all_prover_mode_strategies([subset_unify,comp_fe,un_fe]).   

%%% the atom selection strategy (default: cfirst)
strategy(cfirst).                 % "constraint first"
%strategy(ordered).               % as they occur in the formula
%strategy(cfirst(UserPredList)).  % UserPredList is a list of user defined predicates to be
                                  % executed just after constraint solution (before all other
                                  % user-defined predicates)
                                  % e.g., strategy(cfirst([ttf_list(_),ttf_nat(_),ttf_int(_),ttf_btype(_)])).

%%% the labeling strategy for the clp(FD) solver (default: the default clp(FD) strategy)
fd_labeling_strategy([]).
%fd_labeling_strategy([ff]).
%fd_labeling_strategy([bisect]).
%fd_labeling_strategy([ff,down,enum]).

%%% list of options for setlog/5 (to be tried in the order they occur)
%setlog5_opts([clpfd,final,noirules,noneq_elim,noran_elim]).
setlog5_opts(try([[int_solver(clpfd)],[int_solver(clpq),final],[noirules],[noneq_elim],[noran_elim]])).

%%% sets with cardinality =< size_limit are always expanded to the corresponding 
%%% extensional set (disregading the execution mode prover/solver)
size_limit(6).

%%%%%%%%%% dealing with other aggregates (multisets, list constraints)

%%% activate/suppress dealing with other aggregates besides sets (default: off = sets only)
%other_aggrs(on).
%other_aggrs(off).

%%%%%%%%%% printing options

%%% type constraints to be printed in the computed answer
type_constraints_to_be_shown([set(_),bag(_),list(_),integer(_),rel(_),pfun(_),pair(_),
                              nset(_),ninteger(_),nrel(_),npfun(_),npair(_)]).   %all
%type_constraints_to_be_shown([]).                                                %none
%type_constraints_to_be_shown([set(_),rel(_),pfun(_),pair(_),
                              %nset(_),ninteger(_),nrel(_),npfun(_),npair(_)]).    %current

%%% prefix of fresh variable names
fresh_variable_prefix([95,78]).    %"_N"
%fresh_variable_prefix([95,77]).   %"_M"

%%%%%%%%%% general

%%% activate/suppress occur-check (default: on)
occur_check(on).
%occur_check(off).

%%% activate/suppress **optional** warning messages (e.g., singleton vars in goals) (default: on)
%warnings(on).
warnings(off).


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%% Starting the {log} interpreter %%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% set the initial counter for new predicate names
:- initialization(nb_setval(newpred_counter,0)).   

% load the library of filtering rules (if any)
:- initialization(load_rwrules_lib).

% load the advanced size solver (if any)
:- initialization(load_size_solver).

% load the type-checker (if any)
:- initialization(load_type_checker).

% load the verification condition generator (if any)
:- initialization(load_vcg).

% print the initial message for interactive use
:- initialization((nl,write('Use ?- setlog_help to get help information about {log}'),nl,nl)).





%size_solver15

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
% Advanced size solver
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
%              by Maximiliano Cristia' and  Gianfranco Rossi
%                              January 2020
%
%                           Revised May 2023
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%size_solver_on.

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%     size  solver      %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%%%%%%%% SAT solver  (by Howe & King) %%%%%

initialise(_).  

search(Clauses, Vars, Sat, _) :-
    sat(Clauses, Vars),
    !,
    Sat = true.
search(_Clauses, _Vars, false, _).

sat(Clauses, Vars) :-
    problem_setup(Clauses), elim_var(Vars).

elim_var([]). 
elim_var([Var | Vars]) :-
    elim_var(Vars), (Var = true; Var = false). 

problem_setup([]). 

problem_setup([Clause | Clauses]) :- 
    clause_setup(Clause),
    problem_setup(Clauses). 

clause_setup([Pol-Var | Pairs]) :-
    set_watch(Pairs, Var, Pol). 

set_watch([], Var, Pol) :- Var = Pol. 
set_watch([Pol2-Var2 | Pairs], Var1, Pol1) :- 
    freeze(Var1,V=u), %u is simply a flag
    freeze(Var2,V=u),
    freeze(V, watch(Var1,Pol1,Var2,Pol2,Pairs)).

watch(Var1, Pol1, Var2, Pol2, Pairs) :- 
    nonvar(Var1) ->
      update_watch(Var1, Pol1, Var2, Pol2, Pairs);
      update_watch(Var2, Pol2, Var1, Pol1, Pairs). 

update_watch(Var1, Pol1, Var2, Pol2, Pairs) :-
    Var1 == Pol1 -> true; set_watch(Pairs, Var2, Pol2). 

%%%%%%%% construct and solve the boolean formula %%%%%

%pi(+F,+Vars,+Neqs,-AdmSol)
pi(F,Vars,_Neqs,AdmSol) :-
    bool_code(F,Vars,L),
    %DBG write('Boolean formula: \n\t'), write(L),nl,%get(_),
    (setof(Vars,sat(L,Vars),Arrs),! ; Arrs=[]),
    %DBG write('Boolean solutions: \n\t'),write(Arrs),nl,get(_),
    %DBG length(Arrs,LArr),write('Number boolean solutions: '),write(LArr),nl,
    powerset(Arrs,AdmSol).
    %DBG write('Admissible solution: \n\t'),write(AdmSol),nl,get(_),
       
%bool_code(+F,+Vars,-L) 
bool_code(F,Vars,L) :-
    bool_code_formula(F,Vars,FL),
    one_true(Vars,VL),
    append(FL,[VL],L).     
       
bool_code_formula(true,_,[]) :- !. 
bool_code_formula((F1 & F),Vars,L) :-
    term_variables(F1,F1Vars),
    setlog:subset_strong(F1Vars,Vars),
    bool_code_constraint(F1,L1),!,
    bool_code_formula(F,Vars,L2),
    append(L1,L2,L).
bool_code_formula((_F1 & F),Vars,L) :-
    bool_code_formula(F,Vars,L).
               
bool_code_constraint(un(X,Y,Z),F) :- !,
    var(X),var(Y),var(Z),          
    var_or_false([X,Y,Z],[A2,B2,C2]),
    F=[[false-C2,true-B2,true-A2],[false-A2,true-C2],[true-C2,false-B2]]. 
bool_code_constraint(disj(X,Y),F) :- !,
    var(X),var(Y),       
    var_or_false([X,Y],[A2,B2]),
    F=[[false-A2,false-B2]].
bool_code_constraint(inters(X,Y,Z),F) :- !,
    var(X),var(Y),var(Z),         
    var_or_false([X,Y,Z],[A2,B2,C2]),
    F=[[false-C2,true-A2],[false-C2,true-B2],[false-A2,false-B2,true-C2]].
bool_code_constraint(subset(X,Y),F) :- !,
    var(X),var(Y),        
    var_or_false([X,Y],[A2,B2]),
    F=[[false-A2,true-B2]].     
bool_code_constraint(diff(X,Y,Z),F) :- !,
    var(X),var(Y),var(Z),         
    var_or_false([X,Y,Z],[A2,B2,C2]),
    F=[[false-C2,true-A2],[false-C2,false-B2],[false-A2,true-B2,true-C2]].

one_true([],[]).
one_true([V|VR],[true-V|VRtrue]) :-
    one_true(VR,VRtrue).

var_or_false([],[]).
var_or_false([X|RX],[V|RV]) :-
    (var(X) -> V=X ; V=false),
    var_or_false(RX,RV).

powerset([],[]).
powerset([_H|T],P) :- powerset(T,P).
powerset([H|T],[H|P]) :- powerset(T,P).


%%%%%%%% construct and solve the arithmetic formula %%%%%

mk_arithm_formula(F,SetVars,Sols,R) :-
    length(Sols,NSols),
    length(ViVars,NSols),
    replace_size(F,SetVars,ViVars,Sols,R).

replace_size(true,_,ViVars,_,R) :- !,
    all_positive(ViVars,R).
replace_size((size(S,N) & F2),SetVars,ViVars,Sols,[N is 0|R] ) :-       
    nonvar(S), S={},!,   
    replace_size(F2,SetVars,ViVars,Sols,R).
replace_size((size(S,N) & F2),SetVars,ViVars,Sols,[N is Expr|R] ) :- 
    member_th(S,SetVars,K),!,     % search variable S in SetVars and returns its index K
    mk_expr(K,Sols,ViVars,Expr),
    replace_size(F2,SetVars,ViVars,Sols,R).
replace_size((F1 & F2),SetVars,ViVars,Sols,[F1|R]) :- 
    F1 = (A neq _B),
    attvar(A),!,   
    replace_size(F2,SetVars,ViVars,Sols,R).
replace_size((F1 & F2),SetVars,ViVars,Sols,[F1|R]) :- 
    F1 =.. [Op,_,_],
    member(Op,[is,=<,<,>=,>,=]),!,   
    replace_size(F2,SetVars,ViVars,Sols,R).
replace_size((_F1 & F2),SetVars,ViVars,Sols,R) :- 
    replace_size(F2,SetVars,ViVars,Sols,R).

mk_expr(_,[],_,0) :-!.
mk_expr(K,[Sol|Sols],[V|Vars],Expr)  :- !,
    nth1(K,Sol,B),           %get the k-th element in Sol and return its value (true/false) in B 
    (B==true,!,Expr = 1*V + Expr1
     ;
     B==false,Expr =  0*V + Expr1
    ),
    mk_expr(K,Sols,Vars,Expr1) .     

member_th(X,[Y|_],1) :-
    X==Y,!.
member_th(X,[_Y|R],N) :-
    member_th(X,R,M),
    N is M + 1.

all_positive([],[]) :- !.
all_positive([V|Vars],[V > 0|R]) :-
    all_positive(Vars,R). 

%%%%%%%% find set variables %%%%%
     
find_setvars(F,Vars,Neqs) :-
    find_size_neq(F,F,[],SizeVars,NewF,Neqs),
    find_vars(NewF,SizeVars,Vars).
       
%find_size_neq(+F,+FAll,+Vars,-NewVars,-NewF,-Neqs)    (new parameter FAll = the whole formula
find_size_neq(true,_,Vars,Vars,true,[]) :- !.
find_size_neq((size(S,_) & F),FAll,Vars,NewVars,NewF,Neqs) :- 
    var(S),        
    setlog:member_strong(S,Vars), !,
    find_size_neq(F,FAll,Vars,NewVars,NewF,Neqs).
find_size_neq((size(S,_) & F),FAll,Vars,NewVars,NewF,Neqs) :- 
    var(S),
    member_constraint(S,FAll,V1,_),V1\==[],!,         
    find_size_neq(F,FAll,[S|Vars],NewVars,NewF,Neqs).
find_size_neq((A neq B & F),FAll,Vars,NewVars,(A neq B & NewF),[A neq B|Neqs]) :- !,
    find_size_neq(F,FAll,Vars,NewVars,NewF,Neqs).
find_size_neq((F1 & F),FAll,Vars,NewVars,(F1 & NewF),Neqs) :- !,
    find_size_neq(F,FAll,Vars,NewVars,NewF,Neqs).

find_vars(_F,[],[]) :- !.  
find_vars(true,Vars,Vars) :- !.   
find_vars(F,[V|Vars],NewVars) :-
    member_constraint(V,F,V1,F1),
    V1 \== [],!,                      
    cond_append(V1,Vars,Vars1),
    find_vars(F1,Vars1,NewVars1),
    cond_append(Vars1,NewVars1,NewVars).
find_vars(F,[_V|Vars],NewVars) :- 
    find_vars(F,Vars,NewVars).

%member_constraint(+V,+F,-NewV,-NewF)     %find all set constraints in F containing variable V and
%                                         %return the new variables (NewV) and the formula without the found constraints  
member_constraint(_V,true,[],true) :- !.      
member_constraint(V,(un(X,Y,Z) & true),[X,Y,Z],true) :-    
    one_of(V,X,Y,Z),!.
member_constraint(V,(un(X,Y,Z) & F),[X,Y,Z|NewV],NewF) :- 
    one_of(V,X,Y,Z),!,
    member_constraint(V,F,NewV,NewF).
member_constraint(V,(disj(X,Y) & true),[X,Y],true) :- 
    one_of(V,X,Y),!.
member_constraint(V,(disj(X,Y) & F),[X,Y|NewV],NewF) :- 
    one_of(V,X,Y),!,
    member_constraint(V,F,NewV,NewF).
member_constraint(V,(subset(X,Y) & true),[X,Y],true) :- 
    one_of(V,X,Y),!.
member_constraint(V,(subset(X,Y) & F),[X,Y|NewV],NewF) :- 
    one_of(V,X,Y),!,
    member_constraint(V,F,NewV,NewF).
member_constraint(V,(inters(X,Y,Z) & true),[X,Y,Z],true) :- 
    one_of(V,X,Y,Z),!.   
member_constraint(V,(inters(X,Y,Z) & F),[X,Y,Z|NewV],NewF) :- 
    one_of(V,X,Y,Z),!,
    member_constraint(V,F,NewV,NewF).
member_constraint(V,(diff(X,Y,Z) & true),[X,Y,Z],true) :- 
    one_of(V,X,Y,Z),!.    
member_constraint(V,(diff(X,Y,Z) & F),[X,Y,Z|NewV],NewF) :- 
    one_of(V,X,Y,Z),!,
    member_constraint(V,F,NewV,NewF).
member_constraint(V,(X neq Y & true),[X,Y],true) :- 
    var(Y),!,
    (V==X,! ; V==Y).
member_constraint(V,(X neq Y & F),[X,Y|NewV],NewF) :- 
    var(Y),
    one_of(V,X,Y),!,
    member_constraint(V,F,NewV,NewF).
member_constraint(V,(F1 & F),NewV,(F1 & NewF)) :- 
    member_constraint(V,F,NewV,NewF).  

one_of(V,X,_Y,_Z) :- V==X,!.     
one_of(V,_X,Y,_Z) :- V==Y,!.
one_of(V,_X,_Y,Z) :- V==Z.

one_of(V,X,_Y) :- V==X,!.        
one_of(V,_X,Y) :- V==Y.

%cond_append(+L1,+L2,-L3)   
cond_append([],Vars,Vars).
cond_append([V|R],Vars,VarsNew) :-
    cond_append1(V,Vars,Vars1),
    cond_append(R,Vars1,VarsNew).     

cond_append1(V,Vars,Vars) :-
    setlog:member_strong(V,Vars),!.
cond_append1(V,Vars,[V|Vars]).


%%%%%%%% size_solve %%%%%

size_solve(true,_,_) :- !.
size_solve(F,SizeVars,MinSol) :-
    %DBG write('Input formula: \n\t'),write(F),nl,
    find_setvars(F,RVars,Neqs), 
    reverse(RVars,Vars),
    %DBG write('Set variables: '),write(Vars),nl,
    size_solve(F,Vars,Neqs,SizeVars,MinSol).

size_solve(F,SetVars,Neqs,SizeVars,MinSol) :-
%    (SetVars\==[] ->                      
        pi(F,SetVars,Neqs,Sols),
        %DBG write('Subset of boolean solutions: \n\t'),write(Sols),nl,
        mk_arithm_formula(F,SetVars,Sols,ArithmL),     
        %DBG  write('Arithmetic formula 1: \n\t'),write(ArithmL),nl,
        solve_Q_all(ArithmL),
        %DBG write('Arithmetic formula 2: \n\t'),write(ArithmL),nl,
        %DBG write('Sizes: \n\t'),write(AllSizes),nl,
        term_variables(ArithmL,IntVars),  
        %DBG write('Size variables: \n\t'),write(SizeVars),nl,
        (SizeVars \== [],!,
         mk_sum_to_minimize(SizeVars,Sum)
         ;
         Sum = 1
        ),
        %DBG write('Arithmetic variables: \n\t'),write(IntVars),nl,
        bb_inf(IntVars,Sum,_,Vertex),
        %DBG write('Vertex: \n\t'),write(Vertex),nl,
        get_min_sol(SizeVars,IntVars,Vertex,MinSol)
        %DBG ,write('Formula: \n\t'),write(F),nl
        %DBG ,write('Minimum solution: \n\t'), write(MinSol),nl
        .

%%%%%%%% check size constraints in the constraint list CList %%%%%

cond_check_size(RedC,Nsize,MinSol) :-
    %DBG write('number of size constraints: '),write(Nsize),nl,
    (Nsize >= 1 ->        
        b_getval(int_solver,CurrentSlv),        
        b_setval(int_solver,clpq),
        check_size(RedC,MinSol),!,
        b_setval(int_solver,CurrentSlv)
    ;
        MinSol = []
    ).

% MinSol_ is the result of binding size variables to constants according
% to the result of minimizing the sum of these variables. Some times, some 
% of these variables are bound to constants before the minimization algorithm
% is called. MinSol1 gets the minimal solution returned by the minimization
% algorithm; MinSol2 is equal to MinSol1 except that variables names are
% substituted by those of the original formula; MinSol3 takes care of the
% size variables that are bound to constants before the minimization 
% algorithm is called.
check_size(CList,MinSol_) :-    
    %DBG write('\n****** Input formula: '),nl,write(CList),nl,  
    get_formula(CList,Formula,SizeV2,IntF,SizeV1,SizeC),
    %DBG write('****** Simplified formula: '),nl,write(Formula),flush_output,
    %DBG write('****** SizeVars: '),nl,write(SizeVars),nl,
    copy_term([Formula,SizeV2,IntF,SizeV1,SizeC],[FormulaNew,SizeV2New,IntFNew,SizeV1New,SizeCNew],_),
    %DBG write('****** Simplified formula copied: '),nl,write(FormulaNew),nl,%get(_),   
    %DBG write('****** SizeVarsNew: '),nl,write(SizeVarsNew),nl,
    solve_with_inf_rules(FormulaNew,SizeV1New,IntFNew,SizeCNew),
    size_solve(FormulaNew,SizeV2New,MinSol1),
    %DBG write('****** MinSol1: '),nl,write(MinSol1),nl,
    substitute_vars_minsol(MinSol1,SizeV2New,SizeV2,MinSol2),
    %DBG write('****** MinSol2: '),nl,write(MinSol2),nl,
    bind_size_vars_not_in_minsol(SizeV2,SizeV2New,MinSol3),
    %DBG write('****** MinSol3: '),nl,write(MinSol3),nl,
    append(MinSol2,MinSol3,MinSol_)
    %DBG ,write('****** MinSolFinal: '),nl,write(MinSol_),nl
    .

% bind_size_vars_not_in_minsol(SizeVars,SizeVarsNew,MinSol)
% Some size variables are bound to values after calling solve_Q_all(ArithmL)
% in size_solve/5. Since the size check is done over a copy of the original
% formula, these variables aren't bound to those values in the orginal
% formula. This might make the minimal not really the minimal one.
% This predicate walks through the list of size variables in the
% original formula (SizeVars) and when in the corresponding position of the 
% list of size variables of the copy there's a constant an equality is added
% to MinSol.
bind_size_vars_not_in_minsol([],_,[]) :- !.
bind_size_vars_not_in_minsol([X|SizeVars],[C|SizeVarsNew],MinSol) :-
    integer(C),!,
    MinSol = [X = C | MinSol_],
    bind_size_vars_not_in_minsol(SizeVars,SizeVarsNew,MinSol_).
bind_size_vars_not_in_minsol([_|SizeVars],[_|SizeVarsNew],MinSol) :-
    bind_size_vars_not_in_minsol(SizeVars,SizeVarsNew,MinSol).

% substitute_vars_minsol(MinSol,SizeVarsNew,SizeVars,MinSol_) 
% substitutes the variables in MinSol by the corresponding variable in
% SizeVars. The variables in MinSol belong to SizeVarsNew
substitute_vars_minsol([],_,_,[]) :- !.
substitute_vars_minsol([X = C|MinSol],SizeVarsNew,SizeVars,MinSol_) :-
  member_th(X,SizeVarsNew,I),!,  % X can be a constant in SizeVarsNew
  nth1(I,SizeVars,X_),
  MinSol_ = [X_ = C|MinSol1],
  substitute_vars_minsol(MinSol,SizeVarsNew,SizeVars,MinSol1).
substitute_vars_minsol([_|MinSol],SizeVarsNew,SizeVars,MinSol_) :-
  substitute_vars_minsol(MinSol,SizeVarsNew,SizeVars,MinSol_).

% get_formula(C,F,SV,IF,S)
%   C: list of constraints
%   F: formula to be solved by Zarba
%   SV: list of the second argument of size constraints
%   IF: list of integer constraints contained in C
%   SS: list of the first argument of size constraints
%   S: list of size constraints contained in C
get_formula([],true,[],[],[],[]) :-!.             
get_formula([glb_state(C)|R],C & D,SV,[C|I],SS,S) :- !,  %add arithmetic constraints (stored in glb_state terms)
    get_formula(R,D,SV,I,SS,S).
get_formula([solved(C,_,_)|R],CD,SV,I,SS,S) :- !,  
    get_formula([C|R],CD,SV,I,SS,S).
get_formula([size(S1,S2)|R],size(S1,S2) & D,[S2|SV],I,[S1|SS],[size(S1,S2)|S]) :-
     var(S1),var(S2),!,
     get_formula(R,D,SV,I,SS,S).
get_formula([size(S1,S2)|R],size(S1,S2) & D,SV,I,[S1|SS],[size(S1,S2)|S]) :-
     var(S1),nonvar(S2),!,
     get_formula(R,D,SV,I,SS,S).
get_formula([C|R],C & D,SV,I,SS,S) :-        %add set constraints in solved form
     solved_set_constraint(C),!,
     get_formula(R,D,SV,I,SS,S).
get_formula([X neq Y|R],C & D,SV,[C|I],SS,S) :-    
     attvar(X),!, 
     (C = (X > Y)
      ;
      C = (X < Y)
     ), 
     get_formula(R,D,SV,I,SS,S).
get_formula([subset(S1,int(A,B))|R],D,SV,I,SS,S) :-  
     var(S1), 
     open_intv(int(A,B)),!,  
     nb_setval(subset_int,true),
     get_formula(R,D,SV,I,SS,S).
get_formula([_C|R],D,SV,I,SS,S) :-
     get_formula(R,D,SV,I,SS,S).

solved_set_constraint(un(X,Y,Z)) :- !,
     var(X),var(Y),var(Z).
solved_set_constraint(subset(X,Y)) :- !,
     var(X),var(Y).
solved_set_constraint(disj(X,Y)) :- !,
     var(X),var(Y).
solved_set_constraint(inters(X,Y,Z)) :- !,
     var(X),var(Y),var(Z).
solved_set_constraint(diff(X,Y,Z)) :- !,
     var(X),var(Y),var(Z).

%%%%% Extra predicates for clpq and clpfd

solve_Q_all([]).
solve_Q_all([true|ConstrList]) :-
     !,
     solve_Q_all(ConstrList).
solve_Q_all([C|ConstrList]) :-             % solve the constraint 'Constr' using the CLP(Q) solver
    solve_Q(C,_),
    solve_Q_all(ConstrList).

% mk_sum_to_minimize(SizeVars,Sum)
% SizeVars = [A,B,C] --> Sum = A+B+C
mk_sum_to_minimize([X],X) :- !.
mk_sum_to_minimize([X|SizeVars],Sum) :-
    mk_sum_to_minimize(SizeVars,Sum1),
    Sum = X + Sum1.

% get_min_sol(SizeVars,IntVars,Vertex)
get_min_sol([],_,_,[]) :- !.
get_min_sol([X|SizeVars],IntVars,Vertex,MinSol) :-
    var(X),!,
    member_th(X,IntVars,I),
    nth1(I,Vertex,Vx),
    MinSol = [X = Vx|MinSol1],
    get_min_sol(SizeVars,IntVars,Vertex,MinSol1).
get_min_sol([_|SizeVars],IntVars,Vertex,MinSol) :-
    get_min_sol(SizeVars,IntVars,Vertex,MinSol).

% inference rules

solve_with_inf_rules(F,SizeVar,IntF,SizeC) :-
  apply_inf_rules(F,SizeVar,SizeC,IntF1),
  (IntF1 = [] ->
      true
  ;
      solve_Q_all(IntF),
      solve_Q_all(IntF1)
  ).

apply_inf_rules(F,SizeVar,SizeC,IntF) :-
  apply_un_irule(F,SizeVar,SizeC,_SizeC1,IntF).
% here apply more inference rules
% append the IntF returned by each rule
% make IntF the result of the append
% use SizeC1 to get the size of set variables
% to which some rule has added a new size constraint

% apply_un_irule(F,SizeVar,SizeC,SizeC1,IntF)
%   F: input formula to the size_solver
%   SizeVar: list of the first argument of the size
%            constraints contained in F
%   SizeC: list of size constraints contained in F
%   SizeC1: list of size constraints generated by the
%           inference rule
%   IntF: the list of integer constraints generated by 
%         the inference rule
% un(A,B,C) & size(A,Na) --> Nc =< Na + Nb
% where Nc and Nb represent the size of C and B
% apply same rule if of size(A,Na), size(B,Nb) or size(C,Nc)
% are in F
apply_un_irule(F,SizeVar,SizeC,SizeC1,IntF) :-
  get_un(F,SizeVar,Un),
  (Un == [] ->
     true
  ;
     generate_constraints_un(Un,SizeC,SizeC1,IntF)
  ).

% get_un(F,SV,U)
% U is a list containing all the un-constraints in F
% such that at least one of its arugments belongs to SC
get_un((un(A,B,C) & F),SizeVar,[un(A,B,C)|Un]) :-
  (contains_var(A,SizeVar),!
  ;
   contains_var(B,SizeVar),!
  ;
   contains_var(C,SizeVar),!
  ),
  get_un(F,SizeVar,Un).
get_un((_ & F),SizeVar,Un) :-
  get_un(F,SizeVar,Un).
get_un(true,_,[]).

generate_constraints_un([],_,[],[]) :-!.
generate_constraints_un([un(A,B,C)|Un],SizeCons,SizeC1,IntF) :-
  get_size(SizeCons,A,Na,Size_A,Int_A),
  get_size(SizeCons,B,Nb,Size_B,Int_B),
  get_size(SizeCons,C,Nc,Size_C,Int_C),
  SizeC2 = [Size_A,Size_B,Size_C|SizeCons],
  IntF = [Nc =< Na + Nb,Int_A,Int_B,Int_C|IntF1],
  generate_constraints_un(Un,SizeC2,SizeC3,IntF1),
  append(SizeC2,SizeC3,SizeC1).

get_size([],A,N,size(A,N),0 =< N) :- !.
get_size([size(B,M)|_],A,N,true,true) :-
  B == A,!,
  M = N.
get_size([_|SizeC],A,N,Size,Int) :-
  get_size(SizeC,A,N,Size,Int).






  
  
























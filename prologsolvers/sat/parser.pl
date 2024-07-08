:- module(parser, [parser/3]).
:- use_module(library(assoc)).
:- use_module(library(lists)).



benchmark('../flopsbenchmarks/chat_80_1.cnf', chat_80_1).
benchmark('../flopsbenchmarks/chat_80_2.cnf', chat_80_2).
benchmark('../flopsbenchmarks/chat_80_3.cnf', chat_80_3).
benchmark('../flopsbenchmarks/chat_80_4.cnf', chat_80_4).
benchmark('../flopsbenchmarks/chat_80_5.cnf', chat_80_5).
benchmark('../flopsbenchmarks/chat_80_6.cnf', chat_80_6).
benchmark('../flopsbenchmarks/uf20-0903.cnf', 'uf20-0903').
benchmark('../flopsbenchmarks/uf50-0429.cnf', 'uf50-0429').
benchmark('../flopsbenchmarks/uf100-0658.cnf', 'uf100-0658').
benchmark('../flopsbenchmarks/uf150-046.cnf', 'uf150-046').
benchmark('../flopsbenchmarks/uf250-091.cnf', 'uf250-091').
benchmark('../flopsbenchmarks/uuf50-0168.cnf', 'uuf50-0168').
benchmark('../flopsbenchmarks/uuf100-0592.cnf', 'uuf100-0592').
benchmark('../flopsbenchmarks/uuf150-089.cnf', 'uuf150-089').
benchmark('../flopsbenchmarks/uuf250-016.cnf', 'uuf250-016').
benchmark('../flopsbenchmarks/2bitcomp_5.cnf', '2bitcomp_5').
benchmark('../flopsbenchmarks/flat200-90.cnf', 'flat200-90').

%benchmark('../benchmarks/sudoku.cnf', sudoku).
%benchmark('../benchmarks/small.cnf', small).
%benchmark('../benchmarks/uf20-0694.cnf', 'uf20-0694'). 
%benchmark('../benchmarks/uf50-0987.cnf', 'uf50-0987').
%benchmark('../benchmarks/aim-50-1_6-no-1.cnf', 'aim-50-1_6-no-1').
%benchmark('../benchmarks/uuf50-0102.cnf', 'uuf50-0102'). 
%benchmark('../benchmarks/uuf50-0479.cnf', 'uuf50-0479').
%benchmark('../benchmarks/aim-100-1_6-no-1.cnf', 'aim-100-1_6-no-1').
%benchmark('../benchmarks/aim-100-1_6-yes1-4.cnf', 'aim-100-1_6-yes1-4'). 
%benchmark('../benchmarks/aim-200-3_4-yes1-4.cnf', 'aim-200-3_4-yes1-4'). 
%benchmark('../benchmarks/aim-200-6_0-yes1-1.cnf', 'aim-200-6_0-yes1-1').
%benchmark('../benchmarks/uf100-0386.cnf', 'uf100-0386').
%benchmark('../benchmarks/uuf100-0694.cnf', 'uuf100-0694'). 

parser(Name, NG_Clauses, NG_Vars) :-	
	benchmark(File, Name),
	open(File, read, Stream),
	read_literals(Stream, Literals),
	close(Stream),
	read_clauses(Literals, [], Clauses),
	empty_assoc(Assoc1),
	nonground_clauses(Clauses, Assoc1, Assoc2, NG_Clauses),
	assoc_to_list(Assoc2, NG_List),
	pairs_to_vars(NG_List, 1, NG_Vars).	
	
nonground_clauses([], Assoc, Assoc, []).
nonground_clauses([Clause | Clauses], Assoc1, Assoc3, [NG_Clause | NG_Clauses]) :-
	nonground_clause(Clause, Assoc1, Assoc2, NG_Clause),
	nonground_clauses(Clauses, Assoc2, Assoc3, NG_Clauses).

nonground_clause([], Assoc, Assoc, []).
nonground_clause([Literal | Clause], Assoc1, Assoc3, [true-Var | NG_Clause]) :-
	Literal > 0,
	get_assoc(Literal, Assoc1, Var),
	!,
	nonground_clause(Clause, Assoc1, Assoc3, NG_Clause).
nonground_clause([Literal | Clause], Assoc1, Assoc3, [true-Var | NG_Clause]) :-
	Literal > 0,
	!,
	put_assoc(Literal, Assoc1, Var, Assoc2),
	nonground_clause(Clause, Assoc2, Assoc3, NG_Clause).
nonground_clause([Literal | Clause], Assoc1, Assoc3, [false-Var | NG_Clause]) :-
	Literal < 0,
	NegLiteral is -Literal,
	get_assoc(NegLiteral, Assoc1, Var),
	!,
	nonground_clause(Clause, Assoc1, Assoc3, NG_Clause).
nonground_clause([Literal | Clause], Assoc1, Assoc3, [false-Var | NG_Clause]) :-
	Literal < 0,
	NegLiteral is -Literal,
	put_assoc(NegLiteral, Assoc1, Var, Assoc2),
	nonground_clause(Clause, Assoc2, Assoc3, NG_Clause).

read_literals(Stream, Literals) :-
	get_char(Stream, C),
	read_literals(C, Stream, Literals).
	
read_literals(end_of_file, _Stream, Literals) :-
	!,
	Literals = [].
read_literals(' ', Stream, Literals) :-
	!,
	read_literals(Stream, Literals).
read_literals('\n', Stream, Literals) :-
	!,
	read_literals(Stream, Literals).
read_literals('\t', Stream, Literals) :-
	!,
	read_literals(Stream, Literals).
read_literals('c', Stream, Literals) :-
	!,
	read_line_then_literals(Stream, Literals).
read_literals('p', Stream, Literals) :-
	!,
	read_line_then_literals(Stream, Literals).
read_literals(C, Stream, Literals):-
	name(C, [A]),
    	read_literal_then_literals(Stream, [A], Literals).

read_literal_then_literals(Stream, As, Literals) :-
    	get_char(Stream, C),
	read_literal_then_literals(C, Stream, As, Literals).

read_literal_then_literals(C, Stream, As, Literals) :-
    	digit(C), !,
	name(C, [A]),
	read_literal_then_literals(Stream, [A | As], Literals).
read_literal_then_literals(C, Stream, As, Literals) :-
	reverse(As, RevAs),
	name(Literal, RevAs),
	Literals = [Literal | Rest_Literals],
	read_literals(C, Stream, Rest_Literals).

digit('0').  	
digit('1'). 
digit('2'). 
digit('3').
digit('4').
digit('5').
digit('6').
digit('7'). 
digit('8').
digit('9').

read_line_then_literals(Stream, Literals) :-
	get_char(Stream, C),
	read_line_then_literals(C, Stream, Literals).

read_line_then_literals('\n', Stream, Literals) :-
	!,
	read_literals(Stream, Literals).
read_line_then_literals(_C, Stream, Literals) :-
	read_line_then_literals(Stream, Literals).

read_clauses([], [], []).
read_clauses([0 | Literals], Clause, Clauses) :-
	!,
	reverse(Clause, RevClause),
%	format("~w\n", [RevClause]),
	Clauses = [RevClause | RestClauses],
	read_clauses(Literals, [], RestClauses).
read_clauses([Literal | Literals], Clause, Clauses) :-
	read_clauses(Literals, [Literal | Clause], Clauses).

pairs_to_vars([], _Key, []).	
pairs_to_vars([Key-Var | Pairs], Key, [Var | Vars]) :-	
	!,
	Key1 is Key + 1,
	pairs_to_vars(Pairs, Key1, Vars).
pairs_to_vars([KeyPrime-Var | Pairs], Key, Vars) :-	
	Key1 is Key + 1,
	pairs_to_vars([KeyPrime-Var | Pairs], Key1, Vars).


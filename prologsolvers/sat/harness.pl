%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%Harness for SAT solver
%
%author: Jacob Howe and Andy King
%Last edited: 5/4/11/
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

:- use_module(library(timeout)).
:- use_module(parser).
:- use_module(static_var_order).

%:- use_module(sat_solver_core).
%:- use_module(sat_solver_back).
%:- use_module(sat_solver_instrumented).
:- use_module(sat_solver_learning).
%:- use_module(sat_solver_restore).
%:- use_module(sat_solver_freeze).
%:- use_module(sat_solver_when).

main :-
	harness(_File),
	fail.
main.

harness(File) :-
	parser(File, Clauses, Vars),
	order_variables(Clauses, Vars, Ordered_Vars),
	statistics(runtime, [Start, _]),
	initialise([]),
	time_out(search(Clauses, Ordered_Vars, Sat, _), 60000, Success),
% 	search(Clauses, Ordered_Vars, Sat, _), Success = success,
	statistics(runtime, [Finish, _]),
	Time is Finish - Start,
	length(Clauses, NClauses),
	length(Vars, NVars),
	harness_aux(Success, Sat, File, NClauses, NVars, Time, Vars).

harness_aux(timeout, _Sat, File, NClauses, NVars, Time, _Vars) :-
	format("~w~c~w/~w~c>~w~n", [File, 9, NVars, NClauses, 9, Time]).
harness_aux(success, true, File, NClauses, NVars, Time, _Vars) :-
%	trim(Vars, TrimVars, 32),
	format("~w~c~w/~w~c~w~c~w~n", [File, 9, NVars, NClauses, 9, Time, 9, sat]).
harness_aux(success, false, File, NClauses, NVars, Time, _Vars) :-
	format("~w~c~w/~w~c~w~c~w~n", [File, 9, NVars, NClauses, 9, Time, 9, unsat]).

%trim([], [], _).
%trim([_ | _], [...], 0) :- !.
%trim([true | Vs], [1 | Ts], N) :-
%	N >= 0, !,
%	N1 is N - 1,
%	trim(Vs, Ts, N1).
%trim([false | Vs], [0 | Ts], N) :-
%	N >= 0, 
%	N1 is N - 1,
%	trim(Vs, Ts, N1).


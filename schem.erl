-module(schem).
-export([repl/0, eval_sequence/3, process_seq_eval/2, setup_environment/0]).

%% 
list_car(List) ->
    hd(List).

list_cdr(List) ->
    tl(List).

list_cons(Head, Tail) ->
    if
	is_list(Tail) -> 
	    [Head|Tail];
	true -> [Head, Tail]
    end.

list_set_car(List, Head) ->
    Tail = tl(List),
    list_cons(Head, Tail).

%list_set_cdr(List, Tail) ->
%    Head = list_car(List),
%    list_cons(Head, Tail).

%% 求值环境
make_frame([], [], Frame) ->
    Frame;

make_frame([Var|Vars] ,[Val|Vals], Frame) ->
    NFrame = add_binding_to_frame(Var, Val, Frame),
    make_frame(Vars, Vals, NFrame).

first_frame(Env) ->
    list_car(Env).

add_binding_to_frame(Var, Val, Frame) ->
    dict:store(Var, Val, Frame).   

enclosing_environment(Env) ->
    list_cdr(Env).

extend_environment(Vars, Vals, BaseEnv) ->
    if
	length(Vars) == length(Vals) ->
	    list_cons(make_frame(Vars, Vals, dict:new()), BaseEnv);
	length(Vars) =< length(Vals) ->
	    io:format("Too many arguments supplied, ~p ~p ~n", [Vars, Vals]),
	    exit(error);
	length(Vars) >= length(Vals) ->
	    io:format("Too few arguments supplied, ~p ~p ~n", [Vars, Vals]),
	    exit(error)
    end.

getval_from_frame(Var, Frame) ->
    dict:fetch(Var, Frame).

lookup_variable_value('#t', _) ->
    true;

lookup_variable_value('#f', _) ->
    false;

lookup_variable_value(Var, []) ->
    io:format("Unbound variable ~p ~n", [Var]);

lookup_variable_value(Var, Env) ->
    %% 从本地的环境中获取结果
    Frame = first_frame(Env),
    case dict:is_key(Var, Frame) of
        true -> getval_from_frame(Var, Frame);
        _ -> lookup_variable_value(Var, enclosing_environment(Env))
    end.

get_value_from_process(Pid) ->
    %% 从计算进程获取结果
    case get(Pid) of
        undefined ->
            Pid ! {self(), value},
            receive
                {Pid, ok, Result} ->
                    put(Pid, Result),
                    Result;
                {Pid, Status, _} ->
                    io:format("Error occurs in computation: ~p ~p ~n", [Pid, Status])
            end;
        Re -> Re
    end.

set_variable_value(_, _, []) ->
    [];

set_variable_value(Var, Val, Env) ->
    Frame = first_frame(Env),
    case dict:is_key(Var, Frame) of
        true -> list_set_car(Env, add_binding_to_frame(Var, Val, Frame));
        _ -> list_cons(Frame, set_variable_value(Var, Val, enclosing_environment(Env)))
    end.

define_variable(Var, Val, Env) ->
    Frame = first_frame(Env),
	list_set_car(Env, add_binding_to_frame(Var, Val, Frame)).

inc_depth() ->
    case get(depth) of 
        undefined -> put(depth, 1);
        Depth -> put(depth, Depth+1)
    end.

dec_depth() ->
    case get(depth) of
        undefined -> exit(error_depth);
        1 -> erase(depth);
        Depth -> put(depth, Depth-1)
    end.

%eval
eval(Exp, Env)        ->
    %io:format("eval: ~p     By: ~p ~n", [Exp, self()]),
    case Exp of
	_ when is_number(Exp) -> Exp;                   %% self_evaluating
	_ when is_atom(Exp) -> lookup_variable_value(Exp, Env);   %% symbol = atom
	['define'| _] -> eval_definition(Exp, Env);
	['quote'| _] -> text_of_quotation(Exp);
	['set!'| _] -> eval_assignment(Exp, Env);
	['if'| _] -> eval_if(Exp, Env);
    ['begin'|BeginActions] -> eval_sequence(BeginActions, Env, empty);
	['lambda'| _] -> make_procedure(lambda_parameters(Exp), lambda_body(Exp), Env);
	_ when is_list(Exp) ->
            case io_lib:printable_list(Exp) of
                true -> Exp;            %% string
                _ ->
                    inc_depth(),
                    Args = list_of_values(operands(Exp), Env),
                    dec_depth(),
                    myapply(actual_value(operator(Exp), Env), Args)
            end;
	_ -> io:format("Unknow_expression_type ~p ~n", [Exp]),
	     exit(error)
    end.

eval_sequence([], _, Result) ->
    force_it(Result);

eval_sequence([Exp|Exps], Env, Result) ->
    Re = actual_value(Exp, Env),
    case Re of
        {env, NewEnv} -> eval_sequence(Exps, NewEnv, Result);
        _ -> eval_sequence(Exps, Env, Re)
    end.    

%% definition
definition_variable(Exp) ->
     case  A = list_car(list_cdr(Exp)) of
	 _ when is_atom(A) -> A;
	 _ -> list_car(A)
     end.

definition_values(Exp) ->
    case A = list_car(list_cdr(Exp)) of
	_ when is_atom(A) ->  list_car(list_cdr(list_cdr((Exp))));
	_ -> make_lambda(list_cdr(A), list_cdr(list_cdr((Exp))))
    end.

eval_definition(Exp, Env) ->
    inc_depth(),
    NewEnv = define_variable(definition_variable(Exp), eval(definition_values(Exp), Env), Env),
    dec_depth(),
    {env, NewEnv}.    

%% quote
text_of_quotation(Exp) ->
    list_car(list_cdr((Exp))).

%% assignment
assignment_variable(Exp) ->
    list_car(list_cdr(Exp)).

assignment_value(Exp) ->
    list_car(list_cdr(list_cdr(Exp))).

eval_assignment(Exp, Env) ->
    inc_depth(),
    NewEnv = set_variable_value(assignment_variable(Exp), eval(assignment_value(Exp), Env), Env),
    dec_depth(),
    {env, NewEnv}.

%% if
if_predicate(Exp) ->
    list_car(list_cdr(Exp)).

if_consequent(Exp) ->
    list_car(list_cdr(list_cdr(Exp))).

if_alternative(Exp) ->
    case list_cdr(list_cdr(list_cdr(Exp))) of
	[] ->
	    false;
	_ -> list_car(list_cdr(list_cdr(list_cdr(Exp))))
    end.

eval_if(Exp, Env) ->
    Re = actual_value(if_predicate(Exp), Env),
    case Re of
        false ->
            eval(if_alternative(Exp), Env);
        _ -> 
            eval(if_consequent(Exp), Env)
    end.

%% lambda
lambda_parameters(Exp) ->
    list_car(list_cdr(Exp)).

lambda_body(Exp) ->
    list_cdr(list_cdr(Exp)).

make_lambda(Pars, Body) ->
    list_cons(lambda, list_cons(Pars, Body)).

make_procedure(Pars, Body, Env) ->
    [procedure, Pars, Body, Env].

    
%% apply
operator(Exp) ->
    list_car(Exp).

operands(Exp) ->
    list_cdr(Exp).

first_operand(Ops) ->				
    list_car(Ops).

rest_operands(Ops) ->
    list_cdr(Ops).

list_of_values(Expes, Env) ->
    case Expes of
	[] ->
	    [];
	_ ->
	    list_cons(eval(first_operand(Expes), Env), list_of_values(rest_operands(Expes), Env))
    end.

myapply(Procedure, Args) ->
    case Procedure of
	[primitive| _] ->
	    apply_primitive_procedure(Procedure, list_of_force_args(Args));
	[procedure| _] ->
        %io:format("myapply, sendout procedure body: ~p args: ~p ~n", [procedure_body(Procedure), Args]),
        case get(depth) of
                undefined ->
                    eval_sequence(procedure_body(Procedure), extend_environment(procedure_parameters(Procedure), Args, procedure_environment(Procedure)), empty);
                _ -> 
                    Pid = spawn_link(schem, process_seq_eval, [procedure_body(Procedure), extend_environment(procedure_parameters(Procedure), Args, procedure_environment(Procedure))]),
                    [delay, Pid]
        end;
	_ -> io:format("Unkonwn procedure type --MYAPPLY ~p , Args ~p ~n", [Procedure, Args])
    end.

list_of_force_args(Args) ->
    case Args of
	[] ->
	    [];
	_ ->
	    list_cons(force_it(list_car(Args)), list_of_force_args(list_cdr(Args)))
    end.

actual_value(Exp, Env) ->
    force_it(eval(Exp, Env)).

force_it(Obj) ->
    case Obj of
	[delay|_] ->
	    get_value_from_process(delay_pid(Obj));
	_ -> Obj
    end.

delay_pid(Delay) ->
    list_car(list_cdr(Delay)).

procedure_parameters(P) ->
    list_car(list_cdr(P)).

procedure_body(P) ->
    list_car(list_cdr(list_cdr(P))).

procedure_environment(P) ->
    list_car(list_cdr(list_cdr(list_cdr(P)))).


%% Run environment
apply_primitive_procedure(P, Args) ->
    apply_in_underlying_erlang(P, Args).

primitive_implementation(P) ->
    list_car(list_cdr(P)).

apply_in_underlying_erlang(P, Args) ->
    apply(primitive_implementation(P), Args).

%% primitive procedures
is_null(List) ->
    case List of
        [] -> true;
        _ -> false
    end.

is_true(Obj) ->
    case Obj of
        true -> true;
        false -> false
    end.

setup_environment() ->
    Vars = [car, cdr, cons, '+', '-', '*', '/', '=', '<', '>', sleep, 'true?', 'null?', 'pair?', 'exit'],
    Vals = [[primitive, fun (L) -> list_car(L) end], 
            [primitive, fun (L) -> list_cdr(L) end], 
            [primitive, fun (A, B) -> list_cons(A, B) end], 
            [primitive, fun (A, B) -> A+B end],
            [primitive, fun (A, B) -> A-B end],
            [primitive, fun (A, B) -> A*B end],
            [primitive, fun (A, B) -> A/B end],
            [primitive, fun (A, B) -> A == B end],
            [primitive, fun (A, B) -> A < B end],
            [primitive, fun (A, B) -> A > B end],
            [primitive, fun (Ms) -> timer:sleep(Ms) end],
            [primitive, fun (O) -> is_true(O) end],
            [primitive, fun (L) -> is_null(L) end],
            [primitive, fun (P) -> is_list(P) end],
            [primitive, fun () -> exit(normal) end]], 
    [make_frame(Vars, Vals, dict:new())].

input_prompt() ->
    io:format(">>> ").

out_prompt() ->
    io:format("").

offer_value(Result) ->
    receive 
        {Pid, value} ->
            Pid ! {self(), ok, Result}
%    after 
%            1000 ->
%                io:format("offer_value timeout, ~p ~n", [self()])
    end,
    exit(normal).

process_seq_eval(Exps, Env) ->
    Re = eval_sequence(Exps, Env, empty),
    offer_value(Re).

driver_loop(Env) ->
    input_prompt(),
    Term = lfe_io:read(),
    Output = actual_value(Term, Env),
    case Output of
        {env, NewEnv} ->
            driver_loop(NewEnv);
        _ ->
            out_prompt(),
            lfe_io:print(Output),    
            io:format("~n"),
            driver_loop(Env)
    end.

repl() ->
    io:format("schem.erl V0.1, (exit with ^\\)~n"),
    driver_loop(setup_environment()).


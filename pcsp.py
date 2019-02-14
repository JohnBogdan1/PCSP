from argparse import ArgumentParser, Namespace
from itertools import product, combinations
import operator
import sys
from time import time

# in cazul in care se doreste plot
want_to_plot = False
if want_to_plot:
    import plotly.plotly as py

    # credentiale generate de plotly pe site(username, API Key)
    py.sign_in('username', 'api_key')
    import plotly.graph_objs as go

SUCCESS, FAIL = 0, -1


def read_input_file(in_file):
    """
    Citesc fisierul de intrare si returnez datele citite.
    :param in_file: un string cu numele fisierului de intrare
    :return: n, p, tasks
    """
    tasks = {}
    with open(in_file) as f:
        n, p = map(int, f.readline().strip().split(","))
        for _ in range(n):
            task_info = list(map(int, f.readline().strip().split(",")))
            i, di, ti = task_info[0:3]
            tasks[i] = Namespace(di=di, ti=ti, conds=task_info[3:])
    return n, p, tasks


def write_output_file(out_file, solution):
    """
    Scriu solutia in fisierul de output.
    :param out_file: un string cu numele fisierului de output
    :param solution: dictionar cu liste ca valori
    """
    with open(out_file, "w") as f:
        for proc in solution:
            f.write(str(solution[proc][0]) + "\n")
            for task_assignment in solution[proc][1]:
                f.write(str(task_assignment[0]) + "," + str(task_assignment[1]) + "\n")


def get_constraints(var, constraints):
    """
    Intoarce constrangerile in care este implicata var.
    """
    return [constraint for constraint in constraints if var in constraint[0]]


def fixed_constraints(solution, constraints):
    """
    Intoarce constrangerile care pot fi evaluate.
    """
    return [constraint for constraint in constraints if set(constraint[0]) <= set(list(solution))]


def check_constraint(solution, constraint):
    """
    Evalueaza o constrangere.
    """
    return constraint[1](*[solution[key] for key in constraint[0]])


def overlap(start_a, end_a, start_b, end_b):
    """
    Returneaza True daca exista overlap intre doua sarcini.
    """
    if start_a < end_b and end_a > start_b:
        return True
    return False


def is_unassigned(var, solution):
    """
    Intoarce True daca o variabila nu este deja in solutie.
    """
    return var not in solution


def get_first_unassigned_var(vars, domains, constraints, solution):
    """
    Intoarce prima variabila neasignata din lista de variabile.
    """
    for var in vars:
        if is_unassigned(var, solution):
            return var
    return None


def get_most_constrained_var(vars, domains, constraints, solution):
    """
    Intoarce variabila care este implicata in cele mai multe constrangeri
    in raport cu variabilele inca neinitializate.
    """
    constrained_vars = {}
    for var in vars:
        if is_unassigned(var, solution):
            constrained_vars[var] = 0
            for constraint in constraints:
                if len(constraint[0]) == 2 and var in constraint[0]:
                    other_var_in_constraint = constraint[0][(constraint[0].index(var) + 1) % 2]
                    if is_unassigned(other_var_in_constraint, solution):
                        constrained_vars[var] += 1
    return max(constrained_vars, key=constrained_vars.get)


def minimum_remaining_values(vars, domains, constraints, solution):
    """
    Intoarce variabila care are cele mai putine valori posibile de asignat.
    """
    fails = {}

    for var in vars:
        if is_unassigned(var, solution):
            fails[var] = 0
            for val in domains[var]:

                solution[var] = val
                constraints_list = fixed_constraints(solution, get_constraints(var, constraints))

                for constraint in constraints_list:
                    constraint_result = check_constraint(solution, constraint)

                    if constraint_result == FAIL:
                        fails[var] += 1

            solution.pop(var, None)

    return max(fails, key=fails.get)


def order_vars_by_conds(vars, tasks):
    """
    Ordoneaza variabilele in raport cu conditiile de terminare date in input.
    """
    ordered_vars = []

    for task, value in tasks.items():
        if value.conds:
            for other_task in value.conds:
                if other_task not in ordered_vars:
                    ordered_vars.append(other_task)
            ordered_vars.append(task)

    for var in vars:
        if var not in ordered_vars:
            ordered_vars.append(var)

    return ordered_vars


def get_ordered_vars_by_conds(vars, domains, constraints, solution):
    """
    Obtine prima variabila din lista data de order_vars_by_conds.
    """
    global tasks
    return get_first_unassigned_var(order_vars_by_conds(vars, tasks), domains, constraints, solution)


def is_neighbor(other_var, var, constraints):
    """
    Daca doua variabile sunt vecine in raport cu o constrangere.
    """
    for constraint in constraints:
        if var in constraint[0] and other_var in constraint[0]:
            return True

    return False


def least_constraining_value(var, vars, domains, constraints, solution):
    """
    Ordoneaza valorile crescator dupa numarul de valori eliminate in vecinii
    variabilei curente.
    """
    fails = {}
    for val in domains[var]:
        solution[var] = val
        fails[val] = 0

        for other_var in vars:
            if is_neighbor(other_var, var, constraints) and is_unassigned(other_var, solution):
                for other_val in domains[other_var]:
                    solution[other_var] = other_val

                    constraints_list = fixed_constraints(solution, get_constraints(var, constraints))

                    for constraint in constraints_list:
                        if check_constraint(solution, constraint) == FAIL:
                            fails[val] += 1
                solution.pop(other_var, None)
        solution.pop(var, None)

    sorted_values = sorted(fails.items(), key=operator.itemgetter(1))

    return [p[0] for p in sorted_values]


def default_order(var, vars, domains, constraints, solution):
    """
    Ordinea originala a valorilor.
    """
    return domains[var]


def constraint_propagation(var, val, vars, domains, constraints, solution):
    """
    Elimina valorile care nu sunt consistente cu asignarea var:val din domeniile variabilelor vecine
    cu var care nu au fost inca asignate.
    """
    new_solution = {}
    new_solution[var] = val
    stop_searching = False

    for other_var in vars:
        if is_neighbor(other_var, var, constraints) and is_unassigned(other_var, solution):

            values_to_remove = []

            for other_val in domains[other_var]:
                new_solution[other_var] = other_val

                constraints_list = fixed_constraints(new_solution, get_constraints(var, constraints))

                for constraint in constraints_list:
                    if check_constraint(new_solution, constraint) == FAIL:
                        values_to_remove.append(other_val)
                        break

            new_solution.pop(other_var, None)

            domains[other_var] = [val for val in domains[other_var] if val not in values_to_remove]

            if len(domains[other_var]) == 0:
                stop_searching = True
                break

    return domains, stop_searching


def my_deepcopy(org):
    """
    Creeaza o copie noua a dictionarului org.
    """
    out = dict().fromkeys(org)
    for k, v in org.items():
        try:
            out[k] = v.copy()
        except AttributeError:
            try:
                out[k] = v[:]
            except TypeError:
                out[k] = v

    return out


def PCSP(vars, domains, constraints, acceptable_cost, solution, cost):
    global best_solution
    global best_cost
    global nr_vars
    global select_var_function
    global select_domains_order_function
    global use_propagation
    global start_time
    if want_to_plot:
        global costs
        global times

    # daca am ajuns la o solutie completa
    if len(solution) == n:
        print("New best: " + str(cost) + " - " + str(solution))

        # salvez solutia descoperita
        best_solution = my_deepcopy(solution)
        best_cost = cost

        # salvez timpii si costurile pentru plot
        if want_to_plot:
            costs.append(best_cost)
            times.append(time() - start_time)

        # ma intorc cand am gasit o solutie fezabila
        if best_cost <= acceptable_cost:
            return True
    else:
        # iau o variabila din lista vars folosind o functie
        var = select_var_function(vars, domains, constraints, solution)

        # daca nu mai sunt valori in domeniu, am terminat cautarea
        if not domains[var]:
            return False
        elif cost >= best_cost:
            # daca am ajuns la un cost cel putin mai bun, nu se continua mai departe
            return False

        # ordonez valorile
        ordered_domains = select_domains_order_function(var, vars, domains, constraints, solution)
        var_constraints = get_constraints(var, constraints)

        # pentru fiecare valoare din domeniu
        for val in ordered_domains:

            # asignez acea valoare la variabila
            solution[var] = val

            # daca se doreste propagare de constrangeri la vecini
            if use_propagation:
                propagated_domains, stop_searching = constraint_propagation(var, val, vars, my_deepcopy(domains),
                                                                            constraints,
                                                                            solution)

                # daca am gasit un domeniu gol al unui vecin neasignat inca, nu are rost sa continuam cu backtracking
                if stop_searching:
                    solution.pop(var, None)
                    continue
            else:
                propagated_domains = domains

            # lista constrangerilor ce pot fi evaluate acum
            constraints_list = fixed_constraints(solution, var_constraints)

            # calculez noul cost
            new_cost = cost
            any_constraint_failed = False
            for constraint in constraints_list:
                constraint_result = check_constraint(solution, constraint)

                # daca am gasit o constrangere incalcata, nu merg mai departe
                if constraint_result == FAIL:
                    any_constraint_failed = True
                    break

                new_cost += constraint_result

            # daca noul cost este mai mic decât cel mai bun cost si nu este nicio constrangere incalcata
            if not any_constraint_failed and new_cost < best_cost:
                # rezolvam pentru restul variabilelor
                # daca apelul recursiv intoarce True, a fost gasita o solutie fezabila
                if PCSP(vars, propagated_domains, constraints, acceptable_cost, solution, new_cost):
                    return True

            # elimin asignarea
            solution.pop(var, None)

        return False


def my_plot(vars, domains, constraints, var_function, domains_function, propagation, acceptable_cost):
    global best_solution
    global best_cost
    global select_var_function
    global select_domains_order_function
    global use_propagation
    global start_time
    global costs
    global times

    best_solution = {}
    best_cost = float('inf')

    start_time = time()
    costs = []
    times = []
    select_var_function = var_function
    select_domains_order_function = domains_function
    use_propagation = propagation

    print("Run PCSP")
    PCSP(vars, domains, constraints, acceptable_cost, {}, 0)

    trace = go.Scatter(
        x=times,
        y=costs,
        mode='lines',
        name='Algorithm -> [Variables: ' + str(var_function).split(" ")[1] + '] :: [Values: ' +
             str(domains_function).split(" ")[1] + ']<br>Propagation: ' + str(propagation)
    )

    return trace


def main():
    global n
    global tasks
    arg_parser = ArgumentParser()
    arg_parser.add_argument("in_file", help="Problem file")
    arg_parser.add_argument("out_file", help="Solution file")
    args = arg_parser.parse_args()
    n, p, tasks = read_input_file(args.in_file)

    # capatul maxim al timpului este dat de suma di-urilor fiecarei sarcini
    edge = 0
    for _, v in tasks.items():
        edge += v.di

    vars_properties = list(tasks.items())
    vars = list(tasks.keys())
    domains = {v: list(product(list(range(p)), list(range(0, edge)))) for v in tasks}

    # definesc constrangerile ca liste peste o lista de variabile si o functie asociata

    constraints = [([var[0]], lambda val, di=var[1].di, ti=var[1].ti: max(0, val[1] + di - ti)) for var in
                   vars_properties]

    constraints.extend(
        [(list(comb), lambda *args, other_var=comb[1]: FAIL if False in list(
            map(lambda other_val, y=args[0][1]: not ((other_val[1] + tasks[other_var].di) > y), args[1:])) else SUCCESS)
         for var in
         vars_properties for comb in
         list(product([var[0]], var[1].conds))
         if
         var[1].conds])

    constraints.extend([
        ([list(comb)[0][0], list(comb)[1][0]],
         lambda task1_val, task2_val, task1_di=comb[0][1].di, task2_di=comb[1][1].di: FAIL if (
             task1_val[0] == task2_val[0] and overlap(task1_val[1], task1_val[1] + task1_di, task2_val[1],
                                                      task2_val[1] + task2_di)) else SUCCESS)
        for comb in
        combinations(vars_properties, 2)])

    sys.setrecursionlimit(10000)

    # setez variabilele globale si rulez PCSP

    if not want_to_plot:
        global best_solution
        global best_cost
        global select_var_function
        global select_domains_order_function
        global use_propagation

        best_solution = {}
        best_cost = float('inf')

        select_var_function = get_ordered_vars_by_conds
        select_domains_order_function = default_order
        use_propagation = False

        print("Run PCSP")
        PCSP(vars, domains, constraints, 4, {}, 0)

        print("Best found: " + str(best_cost) + " - " + str(best_solution))

        # scriu solutia in fisier
        processors = {proc: [0, []] for proc in range(0, p)}

        for proc in processors:
            proc_tasks = {}
            for k, v in best_solution.items():
                if v[0] == proc:
                    processors[proc][0] += 1
                    proc_tasks[k] = v[1]
            sorted_proc_tasks = sorted(proc_tasks.items(), key=operator.itemgetter(1))
            processors[proc][1].extend(sorted_proc_tasks)

        write_output_file(args.out_file, processors)
    else:

        # fac plot comparisons intre diferiti algoritmi
        trace1 = my_plot(vars, domains, constraints, get_first_unassigned_var, default_order, True, 11)
        trace2 = my_plot(vars, domains, constraints, get_ordered_vars_by_conds, default_order, False, 11)

        data = [trace1, trace2]

        layout = dict(title='PCSP algorithms comparison',
                      xaxis=dict(title='Time(s)'),
                      yaxis=dict(title='Cost'),
                      )

        fig = dict(data=data, layout=layout)

        py.plot(fig, filename='Algorithms comparison')


if __name__ == '__main__':
    main()

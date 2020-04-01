#!/usr/bin/env python
# -*- coding: utf-8 -*-
import os.path
import sys
import copy


class UnsatisfiedException(Exception):
    """
    Exception class used to "break" out of an unsatisfiable branch.
    """
    pass


class Clause:
    """
    Object that represent a single clause. It containes variables as Dict[int, bool] where
    key is variable number and value is it's parity. For examle (1 \/ !2) results in {1: True, 2: False}
    """
    def __init__(self, variables):
        self.variables = variables

    @classmethod
    def from_list(cls, lst):
        """
        Creates Clause object from list of variables.
        """
        return cls({abs(j): j > 0 for j in set(lst)})

    def __copy__(self):
        return Clause(self.variables.copy())

    def __repr__(self):
        return r" \/".join(str(k) if v else "!"+str(k) for k,v in self.variables.items())

    __str__ = __repr__


class Cnf:
    """
    Class that represents a CNF formula. It has list of clauses of type List <Clause> and formula variables as
    Dict[int, (int, int)] where key is variable number and value is a tuple indicating number of positive
    and negative occurrences.
    """
    def __init__(self, variables, clauses):
        self.variables = variables
        self.clauses = clauses

    @classmethod
    def from_list(cls, clause_list, N):
        """
        Creates cnf formula from the list of clauses. Also number of variables should be supplied.
        """
        variables = {
            j: [0, 0] for j in range(1, N + 1)
        }

        clauses = list(set(clause_list))
        for clause in clauses:
            for (var, par) in clause.variables.items():
                variables[var][par] += 1

        # Dict object where we will keep track of negative and positive occurrances of all variables.
        # This wil enable fast heuristics calculation.
        variables_counters = {
            v: (n, p) for (v, (n, p)) in variables.items()
            if n != 0 or p != 0
        }

        return cls(variables_counters, clauses)

    def unit_propagate(self):
        """
        Gets get unit clause in formula. If empty clause is found UnsatisfiedException is raised.
        After unit clause is found its variable is propagated and resulting assignements are returned
        """
        assigned = {}
        while True:
            if len(self.clauses) == 0:
                return assigned
            for clause in self.clauses:
                if len(clause.variables) == 0:
                    # Empty clause found
                    raise UnsatisfiedException()
                if len(clause.variables) == 1:
                    # Unit clause found
                    for var, par in clause.variables.items():
                        break
                        assigned[var] = par
                    prop = self.propagate({var: par})

                    # Python >= 3.5 supports merging of dict like objects using kwargs.
                    assigned = {**assigned, **prop}
                    break
            else:
                break
        return assigned

    def propagate(self, var_queue):
        """
        Propagate variables in a formula. If contradiction is found UnsatisfiedException is raised.
        """

        assumptions = {}
        while var_queue:
            # Keep track of new clauses
            new_clauses = []

            # Assign variable
            assume_var, assume_val = var_queue.popitem()
            assumptions[assume_var] = assume_val

            # Delete assigned variable from formula.
            try:
                del self.variables[assume_var]
            except KeyError:
                continue

            # Iterate throught clauses and propagate assigned variable
            for clause in self.clauses:

                # parity of assumed variable in current clause
                clause_var = clause.variables.get(assume_var, None)

                if clause_var is None:
                    # Current clause does not contain assumed variable -> add it to new formula
                    new_clauses.append(clause)

                # Clause contains assumed variable. Clause variable is of same parity that assumed
                # .I.e. ( T, T) or (F, F)
                elif clause_var == assume_val:

                    for var, par in clause.variables.items():
                        if var == assume_var:
                            ## This variable is already assumed/set -> continue
                            continue

                        # If variable is not already assumed ->
                        # assume it and change vairables counters

                        # Count positive and negative ocurances of current clause variable
                        var_neg, var_pos = self.variables[var]

                        # Positive parity
                        if par:
                            var_pos -= 1
                            if var_pos == 0:
                                if var_neg == 0:
                                    # this variable is not contained in any additional clause -> delete it
                                    del self.variables[var]
                                    continue
                                else:
                                    # this variable has not any positive occurrence -> Add this variable (with opposite parity)
                                    # into queue for propagation

                                    pair = var_queue.get(var, None)
                                    if pair is None:
                                        var_queue[var] = False

                                    elif pair == True:
                                        # There is already conflicting assumption for this variable. Raise exception
                                        raise UnsatisfiedException()
                        # Negative parity
                        else:
                            var_neg -=1
                            if var_neg == 0:
                                if var_pos == 0:
                                    # this variable is not contained in any additional clause -> delete it
                                    del self.variables[var]
                                    continue
                                else:
                                    # this variable has not any negative occurrence -> Add this variable (with opposite parity)
                                    # into queue for propagation
                                    pair = var_queue.get(var, None)
                                    if pair is None:
                                        var_queue[var] = True
                                    elif pair == False:
                                        # There is already conflicting assumption for this variable. Raise exception
                                        raise UnsatisfiedException()

                        # Set new counters for assumed variable
                        self.variables[var] = var_neg, var_pos

                # Current clause contains assumed variable with different parity
                else:

                    # Delete that variable
                    del clause.variables[assume_var]

                    # if clause is empty after removal => this is a contradiction.
                    if len(clause.variables) == 0:
                        raise UnsatisfiedException()

                    # If clause length is 1, then new unit clause is found
                    elif len(clause.variables) == 1:
                        # get variable and parity from clause
                        var, par = next(iter(clause.variables.items()))

                        # Check if this variable is already assumed with different parity
                        pair = var_queue.get(var, None)
                        if pair is None:
                            var_queue[var] = par
                        elif par != pair:
                            # Raise exception if contradiction is found
                            raise UnsatisfiedException()

                    # Otherwise just append resulting clause in new clauses
                    else:
                        new_clauses.append(clause)
            # Set new clauses
            self.clauses = new_clauses

            # If a current iteration new_clauses is empty, satisfying solution is already found!
            if len(self.clauses) == 0:
                for key, val in var_queue.items():
                    assumptions[key] = val
                return assumptions

        return assumptions

    def __repr__(self):
        return r" /\ ".join(str(clause) for clause in self.clauses)

    def __copy__(self):
        return Cnf(copy.deepcopy(self.variables),
                           [j.__copy__() for j in self.clauses])



class Solver:
    """
    Class used for solving cnf formulas. it ready formula in dimacs format and solves it.
    it also writes solution into file.
    """
    def solve(self, formula):
        # First get all pure variables in formula
        try:

            pure_variables = {}
            for var, (n, p) in formula.variables.items():
                if p == 0:
                    pure_variables[var] = False
                elif n == 0:
                    pure_variables[var] = True

            # Propagate pure variables
            variables = formula.propagate(pure_variables)

            # Merge results from dpll
            variables = {**self.dpll(formula), **variables}
            return variables
        except UnsatisfiedException:
            return {0: 1}


    def dpll(self, formula):

        # Get first assigned variables by unit propagation.
        variables = formula.unit_propagate()

        # Choose spliting variable based on some heuristics
        var, assume = self.dynamic_largest(formula.variables)

        # create a copy of formula for spliting decision
        new = formula.__copy__()

        # try propagate assumed variable. If exception happens propagate with opposite parity.
        try:
            propagated = new.propagate({var: assume})

            # Mayge propagated formula is already satisfied
            if len(new.clauses) == 0:
                # Python >= 3.5 supports merging of dict like objects using kwargs.
                return {**propagated, **variables}

            else:
                new_vars = {**self.dpll(new), **propagated}
                return {**variables, **new_vars}

        except UnsatisfiedException:
            pass

        # if execution comes to this line, formula is not satisfiable regarding split variable decision. Therefore
        # assume opposite and propagate
        new = formula.__copy__()
        propagated = new.propagate({var: not assume})

        # if solution is found after propagation
        if len(new.clauses) == 0:
            return {**propagated, **variables}

        # Else recursivley cal dpll procesure
        else:
            new_vars = {**self.dpll(new), **propagated}
            return {**variables, **new_vars}

    def dynamic_largest(self, variables):
        """
        Calculate decison for split variable and its value. Its is a variable
        with most positive and negative occurrances in formula.
        """
        M = 0
        Mvar = None, None
        for var, (neg, pos) in variables.items():
            if pos + neg > M:
                Mvar = var, pos > neg
        return Mvar

    def from_file(self, file_path):
        """
        Reads input file and returns cnf formula.
        """
        clauses = []
        varnum = 0
        with open(file_path, 'r') as file:
            for line in file:
                if line.startswith("c"):
                    continue
                if line.startswith("p"):
                    tmp = line.split()
                    varnum = int(tmp[2])
                    continue

                variables = list(map(int, line.split()))[:-1]
                clauses.append(Clause.from_list(variables))
        return Cnf.from_list(clauses, varnum)

    def to_file(self, file_path, solution):
        """
        Writes a solution into a file.
        """
        string_sol = " ".join([str(var) if val else str(-var) for var, val in solution.items() if var is not None])
        with open(file_path, "w") as file:
            file.write(string_sol)



if __name__ == "__main__":
    try:
        input_file = sys.argv[1]
        output_file = sys.argv[2]

        solver = Solver()
        cnf = solver.from_file(input_file)

        solution = solver.solve(cnf)

        solver.to_file(output_file, solution)
    except Exception as e:
        print("Cannot start execution. " + str(e.args))




























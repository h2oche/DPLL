import sys
from os import getcwd
from os.path import join, exists
import random

################################################################################
# Global
################################################################################
BASE_DIR = getcwd()
SAT = "SATISFIABLE"
UNSAT = "UNSATISFIABLE"
T_CLAUSE, F_CLAUSE, P_CLAUSE = 0, 1, 2
T_FORMULA, F_FORMULA, P_FORMULA = 0, 1, 2

################################################################################
# Util
################################################################################
def var2str(v):
    if v < 0:
        return "!P" + str(v)[1:]
    else:
        return "P" + str(v)
def sat2str(b):
    return SAT if b else UNSAT

################################################################################
# CNF Formula
################################################################################
# Conjunctive Clause 
class Clause:
    def __init__(self, vs, origin = None):
        self.vs = set([int(v) for v in vs])
        self.origin = origin
    def __str__(self):
        return " \\/ ".join([var2str(v) for v in self.vs])
    def partial_assign(self, A):
        new_vs = []
        for v in self.vs:
            if v in A:
                return (T_CLAUSE, None)
            elif (-v) in A:
                continue
            else:
                new_vs.append(v)
        if len(new_vs) == 0:
            return (F_CLAUSE, self)
        return (P_CLAUSE, Clause(new_vs, self.get_origin()))
    def is_unit(self):
        return len(self.vs) == 1
    def get_origin(self):
        return self if self.origin == None else self.origin
    def resolvent(self, other, v):
        new_vs = self.vs.union(other.vs)
        new_vs = new_vs.difference({v, (-v)})
        return Clause(new_vs) if len(new_vs) != 0 else None
    
# CNF Formula
class Formula:
    def __init__(self, nvars, nclauses, clauses = []):
        self.nvars, self.nclauses, self.clauses = nvars, nclauses, clauses
    def __str__(self):
        ret = f"# of clauses: {self.nvars}\n# of vars: {self.nclauses}\n"
        ret += " /\\\n".join(["(" + str(c) + ")" for c in self.clauses])
        return ret
    def add_clause(self, clause):
        self.clauses.append(clause)
    def reset(self):
        new_clauses = [c.get_origin() for c in self.clauses]
        return Formula(self.nvars, self.nclauses, new_clauses)
    def partial_assign(self, A):
        new_clauses = []
        for c in self.clauses:
            c_case, res = c.partial_assign(A)
            if c_case == T_CLAUSE:
                continue
            elif c_case == F_CLAUSE:
                return (F_FORMULA, res)
            elif c_case == P_CLAUSE:
                new_clauses.append(res)
        if len(new_clauses) == 0:
            return (T_FORMULA, None)
        return (
            P_FORMULA,
            Formula(self.nvars, self.nclauses, new_clauses)
        )
# parse input of DIMACS format
def parse_formula(filename):
    input_path = join(BASE_DIR, filename)
    if not exists(input_path):
        raise Exception(f"Invalid file path: {filename}")
    with open(input_path, "r") as f:
        for line in f.readlines():
            line = line.strip()
            # comment
            if line.startswith("c"):
                continue
            # shape
            elif line.startswith("p"):
                _, _, nvars, nclauses = line.split()
                formula = Formula(int(nvars), int(nclauses))
            # clause
            else:
                clause = Clause(line.split()[:-1])
                formula.add_clause(clause)
    return formula

################################################################################
# DPLL 
################################################################################
# F: Formula
# p_A: Valuation(~ partial assignment) = Var x Clause x B
#   - False means it is from deduction step
#   - True means it is from decision step
def DPLL(F, p_A):
    print("========================================")
    print("DPLL")
    print("----------------------------------------")
    print(F)
    print(p_A)
    print("----------------------------------------")
    # util
    def get_variables(p_A):
        return [v for v, _, _ in p_A]
    # unit propagation
    def unit_propagation(F, p_A):
        orig_A = get_variables(p_A)
        f_case, res = F.partial_assign(orig_A)
        # handle base case
        if f_case == T_FORMULA:
            return (T_FORMULA, p_A)
        elif f_case == F_FORMULA:
            return (F_FORMULA, (res, p_A))
        # propagation, res is now new formula
        new_F, new_A = res, set()
        # compute final partial assignment
        def get_final_assignment():
            return p_A + [(v, c, False) for v, c in new_A]
        while True:
            found = False
            for c in new_F.clauses:
                # add variables to new assignment if it is an unit clause
                if c.is_unit():
                    true_v = list(c.vs)[0]
                    # save origin clause to new parital valuation
                    new_A.add((true_v, c.get_origin()))
                    f_case, res = new_F.partial_assign([true_v])
                    if f_case == T_FORMULA:
                        return (T_FORMULA, get_final_assignment())
                    elif f_case == F_FORMULA:
                        c_conflict = res
                        return (F_FORMULA, (c_conflict, get_final_assignment()))
                    elif f_case == P_FORMULA:
                        new_F = res
                    found = True
                    break
            if not found:
                break
        return (P_FORMULA, (new_F, get_final_assignment()))
    f_case, res = unit_propagation(F, p_A)
    print("----------------------------------------")
    print("!!! unit")
    print(f_case, res)
    print("----------------------------------------")
    if f_case == T_FORMULA:
        return (True, get_variables(res))
    elif f_case == F_FORMULA:
        # clause learning
        c_conflict, p_A0 = res
        c_conflict = c_conflict.get_origin()
        for v, c_deduct, from_decision in reversed(p_A0):
            # if assignment is from decision procedure, skip
            has_v = v in c_conflict.vs or (-v) in c_conflict.vs
            if from_decision or not has_v:
                continue
            # create new resolvent
            c_conflict = c_conflict.resolvent(c_deduct, v)
            print("c_deduct", c_deduct)
            print("c_conflict", c_conflict)
            # if refutation found, return UNSAT
            if c_conflict == None:
                return (False, None)
        print(c_conflict)
        # backtrack to a valuation which makes conflict clause to unit
        while len(p_A0) != 0:
            _, _, from_decision = p_A0.pop()
            if not from_decision:
                continue
            c_case, res = c_conflict.partial_assign(get_variables(p_A0))
            if c_case == P_CLAUSE:
                c_learned = res
                assert(c_learned.is_unit())
                new_F = F.reset()
                new_F.add_clause(c_learned)
                return DPLL(new_F, p_A0)
        # should not reach here
        assert(False)
    elif f_case == P_FORMULA:
        # decision procedure(approximate uniform random)
        F0, p_A0 = res
        c = random.choice(F0.clauses)
        v = random.choice(list(c.vs))
        return DPLL(F0, p_A0 + [(v, None, True)])
        
    
################################################################################
# Entry Point 
################################################################################
def main():
    # parse CNF formula from file
    initial_formula = parse_formula(sys.argv[1])
    # run DPLL algorithm
    # initial_valuation = []
    initial_valuation = [(1, None, True)] + [(-2, None, True)] + [(-3, None, True)] + [(4, None, True)]
    isSAT, A = DPLL(initial_formula, initial_valuation)
    # print output
    if isSAT:
        output = ["s", SAT, "v"] + [str(a) for a in sorted(A)] + ["0"]
    else:
        output = ["s", UNSAT]
    print(" ".join(output))
    
main()

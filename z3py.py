from z3 import * 


# if you have sets of assertions for a thing
# which are incompatible, you can create
# multiple instances of a solver
sol = Solver()

# if I have a solver with no assertions is it SAT?

# (declare-const a Bool)
a_new_bool = Bool("a")
# (declare-const b Bool)
b_new_bool = Bool("b")


# Here create several clauses
aOrB = Or([a_new_bool, b_new_bool])
aXorB = Xor(a_new_bool, b_new_bool)

aXorOrB = aOrB == aXorB

# only now do we add them 
sol.add(aXorB)

print(sol.check())

aTrue = a_new_bool == True
bTrue = b_new_bool == True

# recomend an assertion to make the system UNSAT

AndingOfClause = And([aTrue, bTrue])

sol.add(AndingOfClause)
print(sol.check())

# remove all assertions from SAT solver
sol.reset()

def add(x, y):
    return And(Or(x, y), Not(And(x, y)))

# add assertions for equality with sat_prob.smt
sol.add(aTrue)
sol.add(Not(bTrue))
sol.add(Not(add(a_new_bool, b_new_bool)))

# this returns UNSAT 
print(sol.check())

sol.reset()

x1 = BitVecVal(1, 3)
x2 = BitVecVal(3, 3)
x3 = BitVecVal(2, 3)

c = BitVecVal(4, 3)

# continue solving this, using my reference on the right 


x_1_p = BitVec("x_1_p", 3)
x_2_p = BitVec("x_2_p", 3)

#assertion_1 = Or([x_1_p == x1, x_1_p == x2, x_1_p == x3])

#assertion_1 = Or(*[x_1_p == x1, x_1_p == x2, x_1_p == x3])
assertion_1 = Or([x_1_p == x for x in [x1, x2, x3]])
# Or(x_1_p == x1, x_1_p == x2, x_1_p == x3)
# Or([x_1_p == x1, x_1_p == x2, x_1_p == x3])
assertion_2 = Or([x_2_p == x1, x_2_p == x2, x_2_p == x3])

def fancy(a, b):
    return c == a + b

sol.add(assertion_1)
sol.add(assertion_2)
sol.add(x_1_p != x_2_p) 
sol.add(fancy(x_1_p, x_2_p))

print(sol.check())
print(sol.model())



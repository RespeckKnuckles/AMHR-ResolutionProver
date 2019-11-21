# ResolutionProver
A resolution-based prover without equality. Optimized for standard First-order logic, but has been used in non-classical logics as well.

This code uses S-expressions, with FORALL and EXISTS as quantifiers and AND, OR, IF / IMPLIES, IFF, and NOT as operators. Internally, the code uses nested lists, which are essentially S-expressions in Python list form. 

## Example Usage

This code will print a proof of the classic Aristotelian syllogism:
```
F = ["(FORALL x (Man x) (Mortal x))", 
  "(Man Socrates)",
  "(NOT (Mortal Socrates))"]
[result,trace,clauses] = findContradiction(F, 50000, verbose=True)
```

Resolution-based proofs require you to negate the thing you want to prove, but they can also be used in an open-ended way as well. The function oneStepResolution() will apply resolution exactly once to all clauses created from input formulae, and convert the resulting clauses back into first-order formulae. The following code does so, skipping any formulae that are obvious tautologies. Note that it allows single variables (such as 'G') to count as well-formed formulae:
```
F = ["(IFF G (NOT (Prv_PA (QB G))))",
	"G"]
[vars,newFormulae] = oneStepResolution(F, False)
print("Vars:", vars)
print("Formulae found; ignoring (OR x (NOT x)):")
for f in newFormulae:
	#should we skip this formula?
	if f[0]=='OR':
		if f[1][0]=='NOT':
			if f[1][1] == f[2]:
				continue
		elif f[2][0] == 'NOT':
			if f[1] == f[2][1]:
				continue
	print("\t",f)
```

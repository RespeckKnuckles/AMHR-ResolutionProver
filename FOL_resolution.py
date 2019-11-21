"""
FOL resolution code (without equality)
#Author: John Licato, licato@usf.edu
"""
import sys
import random
import re
import time
from collections import defaultdict
from itertools import product as cartesianProduct
from itertools import permutations

__author__="John Licato"

##################################################
###########  STRING PARSING STUFF ################
##################################################

def propStructToString(stringStruct):
	"""given a nested proposition list of STRINGS like [P a1 a2 [P2 b1]], converts to a string
	that is unique based on the formula it represents (so that two strings are equivalent iff they
	came from the same formula"""
	argSeparator = "__@#__"
	nestedStart = "__*(*__"
	nestedEnd = "__*)*__"
	if isinstance(stringStruct, str):
		return stringStruct
	else:
		toReturn = nestedStart + stringStruct[0] + argSeparator
		for i in range(1, len(stringStruct)):
			toReturn = toReturn + propStructToString(stringStruct[i]) + argSeparator
		toReturn = toReturn + nestedEnd
	return toReturn
	
def propStructToSExp(stringStruct, printForests=True):
	"""given a nested proposition list of STRINGS like [P a1 a2 [P2 b1]], converts to a string 
	formatted as an S-expression and returns result.
	if printForests==True, then it prints forests like [['P','A'],['P','B']] as:
		(P A) (P B)
	otherwise it will print it as:
		((P A), (P B))
	"""
	if isinstance(stringStruct, str):
		return stringStruct
	elif type(stringStruct) is list:
		if len(stringStruct)==0:
			return "()"
		elif type(stringStruct[0]) != str: #assume it's a forest
			toReturn = ""
			if printForests:
				toReturn += "("
			toReturn += propStructToSExp(stringStruct[0])
			for t in stringStruct[1:]:
				if printForests:
					toReturn += ","
				toReturn += " " + propStructToSExp(t)
			if printForests:
				toReturn += ")"
			return toReturn
		else: #it's a normal s-expression
			toReturn = "(" + stringStruct[0]
			for i in range(1,len(stringStruct)):
				toReturn = toReturn + ' ' + propStructToSExp(stringStruct[i])
			return toReturn + ")"
	else:
		raise Exception("Don't know how to parse non-strings and non-lists: " + str(stringStruct))

"""Returns a formatted, readable string with indentations, given an S-expression tree. 
Optimized for FOL."""
def printSExpNice(stringStruct, currIndent=0):
	ind = "  "
	if isinstance(stringStruct,str):
		return ind*currIndent + stringStruct
	if not isinstance(stringStruct[0],str):
		raise Exception("Expected predicate symbol, got: " + str(stringStruct[0]))
	s = (ind*currIndent) + '(' 
	if sum([isinstance(st,str) for st in stringStruct])==len(stringStruct) and len(stringStruct) < 4:
		#do it all on one line
		s = s + ' '.join(stringStruct) + ')'
		return s
	else:	
		s = s + stringStruct[0]
		if stringStruct[0]=='FORALL' or stringStruct[0]=='EXISTS':
			# if isinstance(stringStruct[1], list):
				# s += ' ' + str()
			s = s + ' ' + str(stringStruct[1])
			for arg in stringStruct[2:]:
				s += ("\n" + printSExpNice(arg, currIndent+1))
			s += "\n" + (ind*currIndent) + ')'
			return s
		else:
			for arg in stringStruct[1:]:
				s += ("\n" + printSExpNice(arg, currIndent+1))
			s += "\n" + (ind*currIndent) + ')'
			return s
	
def parseTokens(tokens):
	"""Used internally. Given tokens for a single rooted predicate starting at tokens[0],
	so that input would be something like [ '(', 'P', '(', 'Q', 'a', ')', ')'] for P(Q(a)),
	returns a recursive list ["Predicate" arg1 arg2 ... ]"""
	if len(tokens) == 1: #adding this just to allow single symbol metalogical formulas
		if isinstance(tokens[0], str):
			return tokens[0]
	if len(tokens) <= 2:
		raise Exception("Passed end of token list!")
	if tokens[0] != '(':
		raise Exception("Called parseTokens on a non-rooted node!")
	pred = tokens[1]
	if pred=='(' or pred==')':
		raise Exception("there is no predicate here!")
	tokens.pop(0) #remove leading parentheses
	tokens.pop(0) #remove predicate symbol
	#print("tokens")
	#print(tokens)
	#parse arguments
	toReturn = [pred]
	while True:
		if len(tokens)==0:
			raise Exception("reached end of tokens while parsing for arguments!")
		if tokens[0] == ')':
			tokens.pop(0)
			return toReturn
		elif tokens[0] == '(':
			#recurse
			arg = parseTokens(tokens)
			toReturn.append(arg)
		else:
			toReturn.append(tokens[0])
			tokens.pop(0)

def parseExpression(expr, simple=False):
	"""Parses an s-expression to be a nested list."""
	tokensAll = re.findall("#.*[\n\r]|[:a-zA-Z0-9\-_'!]+|\(|\)", expr)
	tokens = [t for t in tokensAll if t[0]!='#' ] #go through and remove all comment lines
# 	print("passing tokens:", tokens)
	allStructure = parseTokens(tokens)
	return allStructure

def symbolInTree(symbol, T):
	if symbol==T:
		return True
	if isinstance(T, str):
		return False
	for arg in T:
		if symbolInTree(symbol, arg):
			return True
	return False

def pE(s):
	return parseExpression(s)

#T = parseExpression("(NOT (FORALL B (IMPLIES (FORALL Y (IMPLIES (IMPLIES (r B) (r Y)) (p (f Y) Y))) (EXISTS X (EXISTS Y (AND (p X Y) (IMPLIES (q (f B) B) (q X Y))))))))")
#print(printSExpNice(T))

##################################################
###########  UNIFICATION STUFF ###################
##################################################

"""Applies substitution sub to formula tree T. A substitution is a dictionary whose
keys are the variables, and values are the terms that replace them (terms can be either
formula trees, or single strings. So the substitution f(b)/X is represented as:
sub["X"] = ['f' 'b']
And the substitution Y/Z is represented:
sub['Z'] = 'Y'
Note: All variable and term names are case sensitive!
"""
def applySubstitution(T, sub):
	if isinstance(T,str):
		if T in sub:
			#print("Returning",sub[T],'for',T)
			return sub[T]
		else:
			#print(T, "not found")
			return T
	return [T[0]] + [applySubstitution(x, sub) for x in T[1:]]

"""Combines newSub with sub, returning the composition sub o newSub."""
def combineSubstitution(sub, newSub):
	allOriginalVars = sub.keys()
	subToReturn = dict()
	for var in sub:
		#apply substitution newSub to sub[var]/sub.
		newTerm = applySubstitution(sub[var], newSub)
		if newTerm != var:
			subToReturn[var] = newTerm
			#print("Adding",newTerm,"/",var)
	#now append the substitutions from newSub, as long as their vars weren't in sub.
	for var in newSub:
		if not var in allOriginalVars:
			subToReturn[var] = newSub[var]
			#print("Addding",newSub[var],"/",var)
	return subToReturn

"""Given two tree expressions of positive literals in FOL, returns the most
general unifier, or False if the expressions cannot be unified. varList is a list of strings
which are the variables in T1 and T2. Note that T1[0] and T2[0] must be either predicates, or 'NOT'."""
def unify(T1, T2, varList):
	if len(T1)!=len(T2) or T1[0]!=T2[0]:
		return False
	#get disagreement set
	def findDisagreement(t1,t2):
		if isinstance(t1,str) or isinstance(t2,str):
			#at least one of them is a string
			if t1!=t2:
				# print("Found disagreement:", t1, "and", t2)
				return [t1,t2]
			else:
				# print(t1, "and", t2, "are the same!")
				return True
		else:
			#examine each argument
			if len(t1)!=len(t2) or t1[0]!=t2[0]:
				return [t1,t2]
			for i in range(1,len(t1)):
				d = findDisagreement(t1[i], t2[i])
				if d!=True:
					return d
			return True #all arguments are the same!
	sub = {}
	while True:	
		#print("Substitutions are now:",sub)
		#print("Expressions are now:\n", printSExpNice(T1), "\n", printSExpNice(T2))
		D = findDisagreement(T1,T2)
		if D==True:
			return sub #expressions are already unified!
		#print("\nDisagreement set:",D)
		if D[0] not in varList and D[1] not in varList:
			return False #cannot unify two non-variables
		if D[0] not in varList:
			D = [D[1], D[0]] 
		#now D is [variable, term(or variable)]
		#is the var contained in the term?
		if symbolInTree(D[0],D[1]):
			return False #cannot unify, variable contained in term
		sub = combineSubstitution(sub, {D[0]:D[1]})
		T1 = applySubstitution(T1, sub)
		T2 = applySubstitution(T2, sub)

# exit()

##################################################
###########  FOL to CNF STUFF ####################
##################################################

def convertToNegationNormalForm(T):
	#go through formula and replace all implications (IMPLIES).
	def replaceNegations(t):
		if isinstance(t,str):
			return t
		if t[0]=='IMPLIES' or t[0]=='IF':
			return ['OR', ['NOT', replaceNegations(t[1])], replaceNegations(t[2])]
		elif t[0]=='IFF':
			return 	['AND', 
					['OR', ['NOT', replaceNegations(t[1])], replaceNegations(t[2])],
					['OR', ['NOT', replaceNegations(t[2])], replaceNegations(t[1])]
					]
		else:
			return [replaceNegations(a) for a in t]
			
	#go through formula and push all negations down.
	def pushNegations(t):
		if isinstance(t,str):
			return t
		if t[0]=='NOT':
			if t[1][0]=='NOT':
				return pushNegations(t[1][1])
			elif t[1][0]=='OR':
				return ['AND'] + [['NOT',pushNegations(arg)] for arg in t[1][1:]]
			elif t[1][0]=='AND':
				return ['OR'] + [['NOT',pushNegations(arg)] for arg in t[1][1:]]
			elif t[1][0]=='FORALL':
				return ['EXISTS', t[1][1], ['NOT', pushNegations(t[1][2])]]
			elif t[1][0]=='EXISTS':
				return ['FORALL', t[1][1], ['NOT', pushNegations(t[1][2])]]
			else:
				#it's a predicate
				return t
		elif t[0]=='AND' or t[0]=='OR':
			return [t[0]] + [pushNegations(arg) for arg in t[1:]]
		elif t[0]=='FORALL' or t[0]=='EXISTS':
			return [t[0], t[1], pushNegations(t[2])]
		else:
			#it's a predicate, so no negations can be pushed further in
			return t

	oldT = replaceNegations(T)
	while True:
		T = pushNegations(oldT)
		if T==oldT:
			break
		oldT = T
	return T
#convertToNegationNormalForm(pE("(NOT (OR (FORALL p (Q p)) (AND (EXISTS p (NOT (P p))) (P q))))"))
		
"""Given a single tree-structured formula list, make sure all quantified variables have unique names"""
def standardizeVariables(T):
	#figure out what variable name will not cause conflict
	def countQuantifiers(T):
		if isinstance(T,str):
			return 0
		if T[0]=='FORALL' or T[0]=='EXISTS':
			return sum([countQuantifiers(arg) for arg in T[1:]]) + 1
		else:
			return sum([countQuantifiers(arg) for arg in T[1:]])
	numQuantifiers = countQuantifiers(T)
	prefix = 'X'
	while True:
		conflictFound = False
		for i in range(numQuantifiers):
			if symbolInTree(prefix + str(i), T):
				conflictFound = True
				break
		if conflictFound:
			prefix = prefix + "_"
		else:
			break
	#rename variables using prefix
	i = 0
	def replaceQuantifiedVars(var, replacement, T):
		nonlocal i
		nonlocal prefix
		if isinstance(T,str):
			if T==var:
				return replacement
			else:
				return T
		if T[0]=='FORALL' or T[0]=='EXISTS':
			#is the variable we're trying to replace overwritten?
			if T[1]==var:	
				#the variable we're trying to replace is no longer in scope, so do nothing
				return T
			else:
				return [T[0], T[1], replaceQuantifiedVars(var, replacement, T[2])]
		else:
			return [T[0]] + [replaceQuantifiedVars(var, replacement, t) for t in T[1:]]		
	def seekQuantifiedVars(T):
		nonlocal i
		nonlocal prefix
		if isinstance(T,str):
			return T
		if T[0]=='FORALL' or T[0]=='EXISTS':
			oldVar = T[1]
			newVar = prefix + str(i)
			i = i+1
			#first, try to replace the variable in the subtree
			newT = [T[0], newVar, replaceQuantifiedVars(oldVar, newVar, T[2])]
			#now continue iterating through it
			return [newT[0], newT[1], seekQuantifiedVars(newT[2])]
		else:
			return [T[0]] + [seekQuantifiedVars(t) for t in T[1:]]
	return seekQuantifiedVars(T)

"""Converts to prenex form. Note that this assumes that convertToNegationNormalForm()
and standardizeVariables() has already been called."""
def convertToPrenex(T):
	if isinstance(T,str):
		return T
	if T[0]=='FORALL' or T[0]=='EXISTS':
		return [T[0], T[1], convertToPrenex(T[2])]
	elif T[0]=='NOT':
		return T #we assume that it's already in negation normal form, so this case won't be used
	elif T[0]=='OR' or T[0]=='AND':
		T = [T[0]] + [convertToPrenex(arg) for arg in T[1:]]
		#now extract the quantifiers from each subtree, in order
		def getQuantifiers(t):
			if isinstance(t,str):
				return [[],t]
			if t[0]=='FORALL' or t[0]=='EXISTS':
				[quantifiers, subtree] = getQuantifiers(t[2])
				return [[[t[0],t[1]]] + quantifiers, subtree]
			else:
				return [[],t]	
		newT = [T[0]]
		allQuantifiers = []
		for child in T[1:]:
			[quantifiers,subtree] = getQuantifiers(child)
			quantifiers.reverse()
			allQuantifiers.append(quantifiers)
			newT.append(subtree)
		for Q in allQuantifiers:
			for [q,v] in Q:
				newT = [q, v, newT]
		return newT
	else: #a predicate formula is already in prenex
		return T

"""Given a formula tree in negation normal form with all quantified variables standardized (unique names), this function 
skolemizes and removes all quantifiers. Returns: [varList, newTreeFormula, highestIndexUnused]. If you are using this multiple 
times on multiple prenex formulae, then it will record how many "f" functions it creates, starting with startingIndex, and 
then return highestIndexUnused so you can pass it to the next call.
"""
def removeQuantifiers(T, currVarsInScope=[], startingIndex=0):
	# print("F:", T, "\n\tIn scope:", currVarsInScope)
	if isinstance(T,str):
		return [[], T, startingIndex]
	#figure out what function name will not cause conflict
	def countQuantifiers(T):
		if isinstance(T,str):
			return 0
		if T[0]=='FORALL' or T[0]=='EXISTS':
			return sum([countQuantifiers(arg) for arg in T[1:]]) + 1
		else:
			return sum([countQuantifiers(arg) for arg in T[1:]])
	numQuantifiers = countQuantifiers(T)
	prefix = 'f'
	while True:
		conflictFound = False
		for i in range(numQuantifiers):
			if symbolInTree(prefix + str(i + startingIndex), T):
				conflictFound = True
				break
		if conflictFound:
			prefix = prefix + "_"
		else:
			break
	#skolemize. Go through all universal quantifiers until we hit an existential, then skolemize it.
	varsInScope = [x for x in currVarsInScope] #deep copy
	# print(varsInScope)
	if T[0] == 'FORALL':
		if T[1] in varsInScope:
			raise Exception("Variable " + v + " appears to have been used in more than one quantifier! Do not call removeQuantifiers() until all var names have been standardized.")
		varsInScope.append(T[1])
		[vlist, newsubformula, newindex] = removeQuantifiers(T[2], varsInScope, startingIndex)
		# vlist = list(set(vlist))
		for v in vlist:
			if v not in varsInScope:
				varsInScope.append(v)
		return [varsInScope, newsubformula, newindex]
	elif T[0] == 'EXISTS':
		#replace the quantified variable with a skolem function
		if len(varsInScope)==0:
			newSymbol = prefix + str(i)
		else:
			newSymbol = [prefix + str(i)] + varsInScope
		i += 1
		#replace all instances of currNode[1] in currNode[2] with newSymbol
		subformula = applySubstitution(T[2], {T[1]:newSymbol})
		[vlist,newsubformula,newindex] = removeQuantifiers(subformula, varsInScope, startingIndex)
		for v in vlist:
			if v not in varsInScope:
				varsInScope.append(v)
		return [varsInScope, newsubformula, newindex]
	else:
		formulaToReturn = [T[0]]
		varsToReturn = []
		for (fi,subformula) in enumerate(T[1:]):
			[vlist,newsubformula,newindex] = removeQuantifiers(subformula, varsInScope, startingIndex)
			startingIndex = newindex
			varsToReturn += vlist
			formulaToReturn.append(newsubformula)
		return [list(set(varsToReturn)), formulaToReturn, startingIndex]


"""Given a formula tree that has had all of the above functions applied to it, returns a list
of clauses, where each clause is a list of literals."""
def convertToCNF(T):
	def isLiteral(T):
		if isinstance(T,str):
			return True
		if T[0]=='NOT' or (T[0]!='OR' and T[0]!='AND'):
			return True
		return False
	def isClause(T):
		if isinstance(T,str):
			return False
		if T[0]=='NOT' or T[0]=='AND':
			return False
		elif T[0]=='OR':
			for l in T[1:]:
				if not isLiteral(l):
					return False
			return True
		#else, it's a predicate
		return False
	def isCNF(T):
		if isinstance(T,str):
			return False
		if T[0]=='OR' or T[0]=='NOT':
			return False
		if T[0]=='AND':
			for c in T[1:]:
				if not isClause(c):
					return False
			return True
		#else, it's a predicate
		return False
		
	#collapses any AND-AND or OR-OR trees
	def collapse(T):
		if T[0]=='AND': #collapse ANDs
			#is one of the children an 'AND' node?
			for i in range(1,len(T)):
				child = T[i]
				# print(i, child)
				if child[0]=='AND':
					#use this one
					# print("Using child:",T)
					T = ['AND'] + [collapse(t) for t in T[1:i]] + collapse(child[1:]) + [collapse(t) for t in T[i+1:]]
		if T[0]=='OR': #collapse ORs
			#is one of the children an 'OR' node?
			for i in range(1,len(T)):
				child = T[i]
				# print(i, child)
				if child[0]=='OR':
					#use this one
					# print("Using child:",T)
					T = ['OR'] + [collapse(t) for t in T[1:i]] + collapse(child[1:]) + [collapse(t) for t in T[i+1:]]
		#if you find any nodes that are AND with one child that is an OR, or vice versa, collapse it
		# print(T)
		if T[0]=='AND' and len(T)==2 and T[1][0]=='OR':
			T = T[1]
		elif T[0]=='OR' and len(T)==2 and T[1][0]=='AND':
			T = T[1]
		return T
			
	def convertToCNF_recursive(T):
		if isCNF(T):
			return T
		if isClause(T):
			#print("here, returning", ['AND', T])
			return ['AND', T]
		if isLiteral(T):
			#print("here2, returning", ['AND', ['OR',T]])
			return ['AND', ['OR', T]]
		if isinstance(T,str):
			raise Exception("Don't know how code got here with single string " + str)
		if T[0]=='AND':
			toReturn = ['AND']
			for i in range(1, len(T)):
				T[i] = convertToCNF_recursive(T[i])
				# print("T[i]:", T[i])
				for clause in T[i][1:]:
					toReturn.append(clause)
			return toReturn
		if T[0]=='OR':
			for i in range(1,len(T)):
				T[i] = convertToCNF_recursive(T[i])
				#the clauses are T[i][1:]
			# print("After converting children to CNF:",T)
			toReturn = ['AND']
			#the new clauses should be take every combination of the clauses in T[i][1:].
			#so if there are two CNF formulae T[1] and T[2], then the new clauses are:
			#T[1][1]+T[2][1], T[1][1]+T[2][2], T[1][1]+T[2][3], ..., T[1][1]+T[2][m],
			#T[1][2]+T[2][1], T[1][2]+T[2][2], ...
			#..., T[1][n]+T[2][m].
			#number of resulting clauses should be (len(T[0])-1)*...*(len(T[n])-1).
			oldClauses = [T[i][1:] for i in range(1,len(T))]
			#print("old clauses:", oldClauses)
			newClauses = list(cartesianProduct(*oldClauses))
			#print("new clauses:", newClauses)
			for group in newClauses:
				newClause = ['OR']
				for C in group:
					newClause = newClause + C[1:]
				toReturn.append(newClause)
			return toReturn
				
			# counters = [0 for i in range(len(T[1:]))] #the index of the clause in each cnf we're combining
			# while True:#for cnf in T[1:]:
			# 	newClause = ['OR']
			# 	# print("counters:", counters)
			# 	for i in range(len(counters)):
			# 		#combine clauses T[i+1][counters[i]]
			# 		newClause += T[i+1][counters[i]+1][1:]
			# 		#print("Adding", T[i+1][counters[i]+1][1:], "from", T[i+1], "child" [counters[i]+1])
			# 	toReturn.append(newClause)
				
			# 	#increment counter; if it's full then we're done
			# 	counterInd = len(counters)-1
			# 	counters[counterInd] += 1
			# 	while True:
			# 		exitLoop = False
			# 		if counters[counterInd] >= len(T[counterInd+1])-1: #carry the 1
			# 			counters[counterInd] = 0
			# 			counterInd -= 1
			# 			if counterInd < 0:
			# 				exitLoop = True
			# 				break
			# 			else:
			# 				counters[counterInd] += 1
			# 		else:
			# 			#print(counters[counterInd], "isn't >=", len(T[counterInd+1]))
			# 			break
			# 	if exitLoop:
			# 		break
			# return toReturn
		
	while True:
		#print("curr:",T)
		if isCNF(T):
			#print("is CNF:",T)
			return [[l for l in c[1:]] for c in T[1:]]
		
		T = collapse(T)
		# print("after collapse:",T)
		T = convertToCNF_recursive(T)
		# print("after convertToCNF:",T)				


##################################################
###########  FOL RESOLUTION STUFF ################
##################################################

"""Checks whether two clauses should be considered equivalent. Returns True or False. Two clauses
C1 and C2 are considered equivalent if: 
There is a way to shuffle the order of the literals in C2 to produce C2', such that there is a substitution S
that transforms C1 into C2' using only variable/variable substitutions.
"""
def clausesEquivalent(C1,C2,varList):
	if C1==C2:
		return True
	if len(C1)!=len(C2):
		return False
	#quick check: count the number of top-level predicates. If they're not equal, then exit.
	numPreds = defaultdict(int)
	for l in C1:
		numPreds[l[0]] += 1
	for l in C2:
		numPreds[l[0]] -= 1
	allEqual = True
	for k in numPreds:
		if numPreds[k]!=0:
			allEqual = False
			break
	if not allEqual:
		return False
	#now do in-depth check. First, get all possible combinations. Note this is factorial complexity on the
	#number of parameters in the literals! So we assume the number of arguments in the literals are not large,
	#otherwise this will run really slowly.
	foundAlignment = False
	for permutation in permutations(C2):
		#can we rule out this ordering?
		gotoNext = False
		for i in range(len(permutation)):
			if C1[i][0] != permutation[i][0] or len(C1[i])!=len(permutation[i]):
				gotoNext = True
				break
		if gotoNext:
			continue
		sub = unify(C1,permutation,varList)
		if sub==False:
			continue
		else:
			allVars = True
			for key in sub:
				if key not in varList:
					allVars = False
					break
				if sub[key] not in varList:
					allVars = False
					break
			if allVars:
				foundAlignment = True
				break
		if foundAlignment:
			break
	return foundAlignment


"""Combine two clauses using resolution, if possible. Returns a list of resolvents/sub pairs,
each of which is [R, s], where:
R = The resolvent, which is a clause (list of literals)
s = The substitution used to combine these
This algorithm will automatically remove duplicate literals in the resolvent clauses. So if C1 
and C2 produce the resolvent [P(a), P(a)], then it'll just return [P(a)]. Literals must be exactly
equal in order for this to happen.
Note that there may be multiple resolvent/substitution pairs. For example, the clauses
[P(x), P(a)] and [-P(y)] produce resolvents [P(a)] and [P(x)].
varList = a list of variable names. Anything not in this list is assumed to be a non-variable."""
def combineClauses(C1, C2, varList):
	toReturn = []
	for l1 in C1:
		for l2 in C2:
			#are l1 and l2 literals with the opposite sign, same predicate, and same # of arguments?
			if ((l1[0]=='NOT') ^ (l2[0]=='NOT')):
				if l1[0]=='NOT':
					baseL1 = l1[1]
					baseL2 = l2
				else:
					baseL1 = l1
					baseL2 = l2[1]
				if baseL1[0]==baseL2[0] and len(baseL1)==len(baseL2):
					mgu = unify(baseL1, baseL2, varList)
					if mgu==False:
						#print("Unification failed!")
						continue
					#successful unification! Create the resolvent clause.
					# print("Unifying literals:",l1,l2,mgu,"from clauses:",C1,C2)
					#first, remove the clauses you resolved, and then apply substitution to all remaining literals
					C1_new = [applySubstitution(l,mgu) for l in C1 if l!=l1]
					C2_new = [applySubstitution(l,mgu) for l in C2 if l!=l2]
					#add the resolvent clause, and ensure the resulting clause has no duplicates
					resolvent = []
					for l in C1_new+C2_new:
						if l not in resolvent:
							resolvent.append(l)
					# 	else:
					# 		print(l,"already in",resolvent)
					# print("Resolvent:",resolvent)
					# for c in resolvent:
					# 	print('\t',c)
					toReturn.append([resolvent,mgu])
	return toReturn


"""Given a list of clauses, each of which is a list of FOL literals, and a list defining the
variable names, this tries to derive the empty clause. Returns [resultCode,trace,clauses], where:
- resultCode is:
	- '0' if empty clause derived.
	- '1' when the number of total clauses exceeds maxNumFormulae
	- '2' when all possible combinations of clauses has been tried and no more are being created
- trace is None if '1' or '2' was returned; otherwise it is a list where: 
	- every item trace[i] is a list of indices of the two clauses in clauses that were used to create the corresponding clause in clauses.
	- For example, if trace[9]==[2,4], then clause[9] was created by resolving clause[2] and clause[4].
	- If clause[i] was given (not derived), then the trace[i] is 'None'.
	- If traceDerivations==False, then the trace is not performed and trace==None.
- clauses is a list of all the clauses that were provided and created.
- If showNumFormulae==True, then every time 1/10 of the capacity is filled, it prints to the screen.
- Benchmarks is a list of formulae (all provided as S-exp strings). Whenever one of these benchmarks is reached,
	then the program prints that it was achieved."""
def folResolution(clauses, varList, maxNumClauses=100, showNumClauses=False, traceDerivations=True, benchmarks=[]):
	benchmarks = [parseExpression(s) for s in benchmarks]
	#combine every clause with every other clause
	pairsAlreadyCombined = set()
	clauses = [clauses[-1]] + clauses[:-1]
	pairsToCheck = [] #ALWAYS has pairs (i,j) where i<j.
	allClauses = clauses
	if traceDerivations:
		trace = [None for c in clauses]
	else:
		trace = None
	for i1 in range(len(clauses)):
		for i2 in range(i1,len(clauses)):
			if i1<i2:
				pairsToCheck.append((i1,i2))
	while len(pairsToCheck)>0:
		numAdded = 0
		# print(pairsToCheck)
		# input()
		(i1,i2) = pairsToCheck.pop(0)
		if (i1,i2) in pairsAlreadyCombined or (i2,i1) in pairsAlreadyCombined or i1==i2:
			continue
		else:
			pairsAlreadyCombined.add((i1,i2))
			#combine C1 and C2 if possible
			for [resolvent,mgu] in combineClauses(clauses[i1],clauses[i2],varList):
				if resolvent in allClauses:
					#print("Skipping; this clause is already here")
					continue
				#check if the resolvent is equivalent to any existing clause
				matchFound = False
				for c in allClauses:
					if clausesEquivalent(resolvent,c,varList):
						matchFound = True
						break
				if matchFound:
					continue
				# bMet = False
				for b in benchmarks:
					if clausesEquivalent(resolvent,[b],varList) or resolvent==[]:
						print("**BENCHMARK MET:",resolvent)
						bMet = True
				# 		break
				# if not bMet:
				# 	continue
						
				# print("Added clause:",resolvent,"from:\n\t",clauses[i1],"\n\t",clauses[i2])
				
				# ignore = input()
				# if ignore.strip()=='i':
				# 	print("Ignoring this resolvent clause; not adding")
				# 	continue #don't add this, debugger said to ignore it
				allClauses.append(resolvent)
				#update pairs to check
				ir = len(allClauses)-1
				for i in range(len(allClauses)-1):
					pairsToCheck.append((i,ir))
				#update trace
				if traceDerivations:
					trace.append([i1,i2])
				if showNumClauses:
					if len(allClauses)%1000==0:#(maxNumClauses/10)==0:
						print("NUMBER OF CLAUSES:",len(allClauses))
							# if len(allClauses)%50==0:
							# 	print("NUMBER OF CLAUSES:",len(allClauses))
				numAdded += 1
				if len(resolvent)==0:
					#print("FOUND EMPTY")
					return [0, trace, clauses]
				if len(allClauses)>maxNumClauses:
					return [1, None, clauses]
		if len(allClauses)>maxNumClauses:
			return [1, None, clauses]
	return [2, None, clauses] #we've checked all possible combinations of clause pairs

"""Given a list of string S-expressions in FOL, converts them all to CNF clauses. Returns [cnf,vars], where cnf is a list of list-structured clauses in CNF, and vars is the list of variables."""
def stringExpressionsToCNF(sExps, verbose=False):
	formulae = [pE(s) for s in sExps]
	if verbose:
		print("\nFORMULAE:")
		for (i,f) in enumerate(formulae):
			print("[" + str(i) + "]:", f)
	#how should I combine these? All one formula?
	bigFormula = ['AND'] + formulae
	if verbose:
		print("\nBIG FORMULA:",bigFormula, len(bigFormula))
	exp = convertToNegationNormalForm(bigFormula)
	if verbose:
		print("\nNNF::",exp, len(exp))
	exp = standardizeVariables(exp)
	if verbose:
		print("\nStandardized::",exp, len(exp))
	# prenex = [convertToPrenex(f) for f in exp[1:]] #split up so it doesn't put universal quantifiers above where they need to be (no longer necessary with new version of removeQuantifiers())
	# if verbose:
	# 	print("\nPrenex::")
	# 	for p in prenex:
	# 		print("\t",p)

	# vars = set()
	# i = 0
	# removedQuantifiers = []
	# for f in prenex:
	# 	[vars_this,f_new,i] = removeQuantifiers(f, i)
	# 	removedQuantifiers.append(f_new)
	# 	# print("vars:", vars, "index:", i, "\nexp:", f_new)
	# 	for v in vars_this:
	# 		vars.add(v)
	# if verbose:
	# 	print("\nSkolemized:")
	# 	for p in removedQuantifiers:
	# 		print("\t",p)
	# 	print("vars:",vars)

	[vars, f, i] = removeQuantifiers(exp)

	# cnf = []
	# for f in removedQuantifiers:
	# 	cnf_this = convertToCNF(f)
	# 	for c in cnf_this:
	# 		if c not in cnf:
	# 			cnf.append(c)
	cnf = convertToCNF(f)
	if verbose:
		try:
			print("\nCNF:: [")
			for c in cnf:
				print('\t', c)
			print("   ]")
		except:
			print("\nCould not print CNF (probably too large)")
	return [cnf, list(vars)]


"""Given a list of string S-expressions in FOL, this determines whether they lead to a contradiction.
Returns True or False if returnTrace==True. Otherwise, returns [found,trace] where:
-'found' is True or False depending on whether a contradiction was found
-'trace' is the sequence of resolutions that led to the contradiction; None if contradiction wasn't found. It is already cleaned up to remove dead-ends.
-'clauses' is the set of clauses referred to by 'trace'; None if contradiction wasn't found.
"""
def findContradiction(sExps, maxClauses=500, benchmarks=[], verbose=False, returnTrace=True):
	[cnf, vars] = stringExpressionsToCNF(sExps, verbose)
	#for clause in cnf:
	#	print(clause)
	[result,trace,clauses] = folResolution(cnf, vars, maxClauses, True, benchmarks=benchmarks)
	if verbose:
		print("RETURNED:", trace)
	if result==0:
		if verbose:
			print("SUCCESS! Number of clauses created: ",len(clauses))
		if returnTrace:
			#backwards iterate through trace and mark all of those that should be kept
			toRemove = set(range(len(trace)))
			toRemove.remove(len(trace)-1) #keep the first element
			linesToCheck = [len(trace)-1]
			while len(linesToCheck)>0:
				i = linesToCheck.pop(0)
				if trace[i]==None: #this clause was given
					continue
				linesToCheck += trace[i]
				for c in trace[i]:
					if c in toRemove:
						toRemove.remove(c)
					# toRemove.remove(trace[i][0])
					# toRemove.remove(trace[i][1])
 			# print("Remove:",toRemove)
			#remove all those that need to be removed, updating line numbers
			toRemove = sorted(list(toRemove), reverse=True)
			for i in toRemove:
				for j in range(i, len(trace)):
					if trace[j]==None:
						continue
					if trace[j][0] >= i:
						trace[j][0] -= 1
					if trace[j][1] >= i:
						trace[j][1] -= 1
				trace.pop(i)
				clauses.pop(i)
			#sort them so that no line refers to lines after it, and update line numbers
			cleanedTrace = [ [clauses[i], trace[i]] for i in range(len(trace))]
			
			if verbose:			
				maxLen = 0
				print('\nPROOF:')
				for c in clauses:
					maxLen = max(maxLen, len(str(c)))
				for i in range(len(cleanedTrace)):
					if cleanedTrace[i][1]==None:
						#find out which original input formula it might have come from
						for (j,f1) in enumerate(sExps):
							f2 = propStructToSExp( ["NOT", ["OR"] + cleanedTrace[i][0]], False)
							# print("F1:", f1, "\n\tF2:", f2)
							[cnf2, vars2] = stringExpressionsToCNF([f1,f2], False)
							(r,_,_) = folResolution(cnf2, vars2, maxClauses, False)
							if r==0:
								cleanedTrace[i][1] = "Input Formula " + str(j)
								break
					n = (maxLen+10) - len(str(cleanedTrace[i][0]))
					print(i, ":", cleanedTrace[i][0], ' '*n, cleanedTrace[i][1])
			
			return [True, cleanedTrace, clauses]
		else:
			return True
	else:
		if verbose:
			print("Could not resolve (Code", result, ")")
		if returnTrace:
			return [False, None, None]
		else:
			return False


"""Given a list of string S-expressions in FOL, this uses resolution to determine which new formulae can be inferred after exactly one step of resolution.
Returns: [vars, newFormulae] where:
- vars: a list of universally-quantified variables used in these formulae
- newFormulae: a list of formulae, in the form of list-structured S-expressions. """
def oneStepResolution(sExps, verbose=False):
	[cnf, vars] = stringExpressionsToCNF(sExps, verbose)
	knownFormulae = set()
	newFormulae = []
	for s in sExps:
		knownFormulae.add( propStructToString( parseExpression(s) ) )
	# for clause in cnf:
	# 	for f in clause:
	# 		knownFormulae.add( propStructToString(f) )
	for c1 in cnf:
		for c2 in cnf:
			if c1==c2:
				continue
			for (clause,substitution) in combineClauses(c1, c2, vars):
				# print("Resolving", c1, "and", c2)
				if len(clause)==0:
					if "⊥" not in knownFormulae:
						knownFormulae.add("⊥")
						newFormulae.append("⊥")
				else:
					if len(clause)==1:
						f = clause[0]
					else:
						f = ["OR"] + clause
					s = propStructToString(f)
					if s not in knownFormulae:
						# print("\tAdding", f)
						knownFormulae.add(s)
						newFormulae.append(f)
	return [vars, newFormulae]


##################################################
###########  TEMPORARY TEST STUFF ################
##################################################
if __name__=="__main__":
	# F = ["(FORALL psi (AND (PROVES PA (Opposite (QB psi) (QB (NOT psi)))) (Opposite (QB psi) (QB (NOT psi)))))",
	# "(FORALL phi (IMPLIES (PROVES PA phi) (Proves (QB phi))))",
	# "(FORALL n (FORALL m (IMPLIES (AND (Opposite n m) (Proves n)) (NOT (Proves m)))))",
	# "(EXISTS phi (AND (PROVES PA phi) (PROVES PA (NOT phi))))"]

	import time
	s = time.time()
	F = ["(EXISTS A (EXISTS B (EXISTS C (EXISTS D (AND (modifier_pp A at B) (AND (predicate1 A wave C) (AND (predicate1 D smile C) (AND (object C child countable na geq 2) (camera B)))))))))",
	"(EXISTS A (AND (NOT (EXISTS B (predicate1 B smile A))) (object A child countable na geq 2)))"]
	[result,trace,clauses] = findContradiction(F, 50000, verbose=True)
	t = time.time() - s
	print("Took",t/60,"minutes")

# 	F = ["(IFF G (NOT (Prv_PA (QB G))))",
# 		"G"]
# 	[vars,newFormulae] = oneStepResolution(F, False)
# 	print("Vars:", vars)
# 	print("Formulae found; ignoring (OR x (NOT x)):")
# 	for f in newFormulae:
# 		#should we skip this formula?
# 		if f[0]=='OR':
# 			if f[1][0]=='NOT':
# 				if f[1][1] == f[2]:
# 					continue
# 			elif f[2][0] == 'NOT':
# 				if f[1] == f[2][1]:
# 					continue
# 		print("\t",f)

	# exp = ['AND', ["FORALL", 'x', ['EXISTS', 'y', ['P', 'x', 'y']]], ["FORALL", 'x', ['EXISTS', 'y', ['P', 'x', 'y']]]]

	# T = pE("(AND (FORALL y (Q y)) (EXISTS x (P x)))")
	# [vars,T2,i] = removeQuantifiers(T, currVarsInScope=[], startingIndex=0)
	# print("Started with:", T)
	# print("Final formula:", T2, "\nvars:", vars, "\nindex unused:", i)
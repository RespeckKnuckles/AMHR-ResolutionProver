import re
import os

__author__="John Licato"

"""This file can be used to parse TPTP problems of a specific type. You can go to
http://tptp.cs.miami.edu/~tptp/cgi-bin/TPTP2T and select the following params to
find .p files that are valid: 

Logical form: FOF
First-order subform: Real 1st order
Status: Theorem
Formulae: I usually keep this to between 1 and 20. Also, keep in mind that imports of axiom files are not currently supported.
Equality: No equality
Unit equality: No
Maximal predicate arity: 2

Author: John Licato, licato@usf.edu
"""


operators = ['=>', '<=>', '&', '|', '=', '!=', '~&', '~|',]
operatorNames = ['IMPLIES', 'IFF', 'AND', 'OR', 'EQUALS', 'NEQUALS', 'NAND', 'NOR']#, 'NOT'] #should correspond 1-to-1 with operators
specialTokens = ['(', ')', '[', ']', ',', '.', ':', '?', '~', '!'] + operators
startSpecial = {op[0] for op in specialTokens} #the starting characters of each operator
whitespace = ['\n', '\t', ' ', '\r', '\t', '\v', '\f']

def tokenize(S):
	currToken = ""
	tokens = []
	currMode = 0 #0 = default / reading whitespace, 1=reading single quote string, 2=reading double quote string, 3=reading operator/special symbol, 4=reading (non-quote) token
	for c in S:
		# print("Curr char:", c, "Mode:", currMode, "Token:", currToken, "Curr tokens:", tokens)
		if currMode==0:
			pass #do nothing; let it pass through
		elif currMode==1 or currMode==2:
			pass #we don't currently process quotation marks. See http://www.cs.miami.edu/home/geoff/Courses/TPTPSYS/TPTPWorld/TPTPProblems for details on how.
		elif currMode==3: #reading an operator currently
			#check list of operators, and look at what they could possibly be writing. 
			#If the possibilities are more than one (e.g., ~ can be ~, ~&, or ~|) then let it keep going.
			#otherwise, consider this a completed operator.
			opCandidate = currToken + c
			possibilities = [t for t in specialTokens if opCandidate==t[:len(opCandidate)]]
			# print("\tPossible operators for ", opCandidate, ":", possibilities)
			if len(possibilities) == 1:
				#we must be building this one operator. Pass and let it happen (if it's wrong, we'll catch it later.)
				currToken += c
				continue
				# tokens.append(opCandidate)
				# currToken = ""
			elif len(possibilities) > 1:
				currToken += c
				continue
			else: #len(possibilities)==0
				#assume we're done with the operator. Is it a valid one?
				if currToken in specialTokens:
					tokens.append(currToken)
					currToken = ""
				else:
					raise Exception("Error: treated '" + currToken + " as an operator, but it's not an actual operator.")	
		else: #currMode==4; reading a token currently
			if c in whitespace or c in startSpecial:
				tokens.append(currToken)
				currToken = ""
			else:
				currToken += c
				continue
		#passthroughs: if we haven't yet processed the current character
		if c in startSpecial:
			currMode = 3
			currToken = c
		elif c in whitespace:
			currMode = 0
			continue
		else:
			currMode = 4
			currToken = c
	if currToken.strip() != '':
		tokens.append(currToken)
	return tokens

"""Given the string containing a single fof formula, converts it to s-notation.
If returnMetadata==True, then it returns (formulaName, formulaType, formula)
If replaceTnF==True, then it replaces $true and $false with equivalent formulas.
If multivar quantifiers==True, then it allows quantifiers with multiple variables like (EXISTS [a,b] P(a,b)).
"""
def translateFOF_formula(S, returnMetadata=False, replaceTnF=True):
	verbose = False#True
	
	if replaceTnF:
		#remove $true and $false symbols
		S = S.replace('$true', '(P(a) | ~ P(a))').replace('$false', '(P(a) & ~ P(a))')
	
	tokens = tokenize(S)
	if tokens[0]=='include':
		raise Exception("This file requires an axiom file to be imported. Currently that isn't supported.")
	if not (tokens[0]=='fof' and tokens[1]=='(' and tokens[-1]=='.' and tokens[-2]==')'):# and tokens[6]=='(' and tokens[-2]==')'):
		raise Exception("Error parsing: this is not a well-formated fof.")
	formulaName = tokens[2]
	formulaType = tokens[4]
	# print(formulaName, formulaType)
	tokens = [t for t in tokens[6:-2] if t!=',']
	if verbose:
		# print(tokens)
		print('   '.join([str(i) + ':\'' + t + "'" for (i,t) in enumerate(tokens)]))
	#begin parsing formula

	def parseExistential(i):
		#i is the index of the first square bracket
		if tokens[i]!='[':
			raise Exception("invalid format for existentially quantified formula, expecting '[', received " + tokens[i+1])
		j = i+1
		curr = tokens[j]
		quantifiedVars = []
		#parse quantified variables
		while curr!=']':
			quantifiedVars.append(curr)
			j += 1
			if j>=len(tokens):
				raise Exception("expecting ']', reached end of token list")
			curr = tokens[j]
		if verbose:
			print("Quantified Vars:", quantifiedVars)	
		#parse quantified formula
		j = j+1
		curr = tokens[j]
		if curr!=':':
			raise Exception("invalid format for existentially quantified formula, expecting ':', received " + tokens[i+1])
		j = j+1
		(k,quantifiedFormula) = parseUnknown(j)
		
		return (k, ['EXISTS', quantifiedVars, quantifiedFormula])
	
	def parseUniversal(i):
		#i is the index of the first square bracket
		if tokens[i]!='[':
			raise Exception("invalid format for universally quantified formula, expecting '[', received " + tokens[i+1])
		j = i+1
		curr = tokens[j]
		quantifiedVars = []
		#parse quantified variables
		while curr!=']':
			quantifiedVars.append(curr)
			j += 1
			if j>=len(tokens):
				raise Exception("expecting ']', reached end of token list")
			curr = tokens[j]
		if verbose:
			print("Quantified Vars:", quantifiedVars)
		#parse quantified formula
		j = j+1
		curr = tokens[j]
		if curr!=':':
			raise Exception("invalid format for universally quantified formula, expecting ':', received " + tokens[i+1])
		j = j+1
		(k,quantifiedFormula) = parseUnknown(j)
		
		return (k, ['FORALL', quantifiedVars, quantifiedFormula])
	
	def parseArgument(i):
		if verbose:
			print("called parseArgument",i,tokens[i])
		#is this a function?
		if tokens[i+1] == '(':
			funcName = tokens[i]
			j = i+2
			curr = tokens[j]
			funcArgs = []
			while curr!=')':
				(j,arg) = parseArgument(j)
				curr = tokens[j]
				funcArgs.append(arg)
			if verbose:
				print("Treating",funcName,"as a function with args", funcArgs)
			return (j+1, [funcName] + funcArgs)
		else: #not a function, return single string
			return (i+1, tokens[i])
	
	def parseNested(i):	
		if verbose:
			print("Opening parentheses at",i)
		(j1, child1) = parseUnknown(i)
		#is the next token an operator, or the end of the nested formula?
		if j1>=len(tokens):
			raise Exception("Expecting ')', reached end of token list!")
		elif tokens[j1]==')':
			if verbose:
				print("Closing parentheses at",j1)
			return (j1+1, child1)
		elif tokens[j1] in operators:
			operator = tokens[j1]
			(j2, child2) = parseUnknown(j1+1)
			#exit; make sure they closed parenthesis
			if tokens[j2]!=')':
				raise Exception("Expecting ')', received " + tokens[j2])
			if verbose:
				print("Creating",operator,"formula with arguments:", child1, child2)
			return (j2+1, [operatorNames[operators.index(operator)], child1, child2])
		else:
			raise Exception("Not sure what to do with token " + tokens[j1] + ". Full token set:" + str(tokens))		
	
	def parseUnknown(i):
		#branch based on the type of tokens[i]. If we return (j,_), then tokens[i:j] must be a wff.
		if tokens[i] == '(':
			(j, child) = parseNested(i+1)
			return (j, child)
		elif tokens[i] == '!':
			(j, child) = parseUniversal(i+1)
			return (j, child)
		elif tokens[i] == '?':
			(j, child) = parseExistential(i+1)
			return (j, child)
		elif tokens[i] == '~':
			(j, child) = parseUnknown(i+1)
			return (j, ['NOT', child])
		else:
			#is it a predicate, or a formula with an infix operator?
			if tokens[i+1]=='(':
				#it's a predicate
				j = i+2
				predicate = tokens[i]
				args = []
				while True:
					if tokens[j]==')':
						if verbose:
							print("Treating",predicate,"as a predicate with args", args)
						return (j+1, [predicate] + args)
					else:
						(k, arg) = parseArgument(j)
						args.append(arg)
						j = k
						if verbose:
							print("\tadding arg",arg)
			# elif tokens[i+1] in ['!=', '=']: 
			# 	#it is an (in)equality formula
			# 	(k,arg2) = parseUnknown(i+2)
			# 	return [tokens[i+1], arg1, arg2]
			else: #it's a symbol rather than a predicate formula
				if verbose:
					print("Assuming that '", tokens[i], "' is either an object or a wff.")
				return [i+1, tokens[i]]
				# raise Exception("Unexpected token: " + tokens[i] + " at index " + str(i) + " (Did you use a propositional symbol accidentally?)")
	
	(i, root) = parseUnknown(0)
	if i<len(tokens):
		#print(i, len(tokens))
		raise Exception("invalid syntax! Extra token " + str(tokens[i]) + " at index " + str(i))
	if returnMetadata:
		return (formulaName, formulaType, root)
	else:
		return root

"""translateFOF_formula returns a formula tree which allows quantifiers to have a list of quantified
variables. This function transforms that formula tree into one with only one quantified variable 
per quantifier."""
def removeDuplicateQuantifiedVars(F):
	if isinstance(F,str):
		return F
	if F[0]=="FORALL" or F[0]=="EXISTS":
		if isinstance(F[1],list):
			#split it up!
			last = removeDuplicateQuantifiedVars(F[2])
			F[1].reverse()
			for q in F[1]:
				currNode = [F[0], q, last]
				last = currNode
			return currNode
	elif F[0]=='NOT':
		return ['NOT', removeDuplicateQuantifiedVars(F[1])]
	else:
		return [removeDuplicateQuantifiedVars(o) for o in F]

"""Converts formula trees (after removeDuplicateQuantifiedVars was called) to string s-expressions."""
def treeToSexp(T):
	if isinstance(T,str):
		return T
	return ("(" + " ".join([treeToSexp(arg) for arg in T]) + ")")

#parses an entire TPTP file
def parseFile(fileName, negateConjectures=False):
	with open(fileName) as F:
		lines = F.readlines()
	unparseableFormats = ['thf', 'tff', 'cnf', 'th1', 'th0', 'tf1', 'tf0']
	formulae = []
	currString = ""
	def addFormula(st):
		(fname, ftype, F) = translateFOF_formula(st, True)
		F2 = removeDuplicateQuantifiedVars(F)
		if ftype=='conjecture':
			F2 = ["NOT", F2]
		elif ftype!='axiom':
			raise Exception("Don't recognize formula type: " + ftype)
		formulae.append(F2)
	for l in lines:
		for u in unparseableFormats:
			if l.startswith(u):
				raise Exception("Don't know how to parse formulae of type: " + u)
		if l.startswith('%'):
			continue #comment line
		elif l.startswith("fof"):
			if currString.strip()!="":
				#flush old formula
				#print("Trying to parse:", currString)
				addFormula(currString)
			currString = l
		elif l.strip()=="":
			continue
		else:
			currString = currString + l
	if currString.strip()!="":
		#flush old formula, if any
		#print("Trying to parse:", currString)
		addFormula(currString)
		
	return formulae
			
if __name__=="__main__":
	testF = """fof(f1, axiom, (
	? [A,B,C,D] : ((P(A)=>P(B)) &
	((predicate2(A,insert,C,D)) &
	((modifier_adv(A,manually,pos)) &
	((card(D)) &
	((customer(C)) &
	(slot(B)))))))))."""

	testF = """fof(part_of_defn,axiom,
		( ! [C,C1] :
			( part_of(C1,C)
		  <=> ! [P] :
				( incident_c(P,C1)
			   => incident_c(P,C) ) ) )).""" 
		   
	testF = """fof(x2115,conjecture,
		( ( (! [X] :
			  ( ? [Y] : big_p(X,Y)
			 => ! [Z] : big_p(Z,Z) )
		  & ! [U] :
			? [V] :
			  ( big_p(U,V)
			  | ( big_m(U)
				& big_q(f(U,V)) ) ))
		  & ! [W] :
			  ( big_q(W)
			 => ~ big_m(g(W)) ) )
	   => ! [U] :
		  ? [V] :
			( big_p(g(U),V)
			& big_p(U,U) ) ))."""

	# testF = """fof(x2115,conjecture,
	#     ( (( ! [X] : P(x)
	#       & ! [U] : Q(x))
	#       & ! [W] : P(x) )))."""
		
	testF = """fof(x,axiom,((P(a) & (Q(b)!=a)) => Q(c)))."""

	# print("Parsing:", testF)
	# print(treeToSexp(translateFOF_formula(testF)))

	# for f in os.listdir("p files"):
	# 	if f[0]=='.':
	# 		print("Skipping", f)
	# 		continue
	# 	print("Processing", f, "...")
	# 	Fs = parseFile("p files/"+f, True)
	# 	with open("sexp files/" + f[:-2] + ".txt", 'w') as outF:
	# 		outF.write('\t[\t"')
	# 		outF.write('",\n\t\t"'.join([treeToSexp(formula) for formula in Fs]))
	# 		outF.write('"]')
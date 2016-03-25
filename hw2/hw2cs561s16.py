# -*- coding: utf-8 -*-
import sys
import copy
import os

######################## structure ######################

#atomic sentence: ~OP(arg1,arg2)
class Atomic(object):
	"""docstring for Atomic"""
	op=""
	args=[]
	def __init__(self, functionName, argumentList):
		self.op=functionName
		self.args = argumentList
	def __eq__(self,other):
		return self.op==other.op and cmp(self.args,other.args)==0
		
#one line is one query: Atomic&&Atomic...=> conclusion
class Clause(object):
	"""docstring for Clause"""
	atomicList=[]
	conclusion=Atomic("",[])
	num=0
	def __init__(self,atomicList,conclusion,n):
		self.atomicList=atomicList
		self.conclusion=conclusion
		self.num=n
	
class Substitution(object):
	"""docstring for Substitution"""
	mapping={}
	timeStamp=0
	isFail=False
	def __init__(self):
		self.mapping={}
		timeStamp=0
		isFail=False
	def found(self,var,val):
		if var in self.mapping:
			return self.mapping[var]==val
	def add(self,var,val):
		res=Substitution()
		res.mapping=self.mapping.copy()
		res.timeStamp=self.timeStamp
		res.isFail=self.isFail
		res.mapping[var]=val
		return res

class VCLC(object):
	"""docstring for variable,constant,list,compound"""
	op=""
	args=[]
	def __init__(self, atomic=None):
		op=""
		args=[]
		if atomic!=None:
			self.op=atomic.op
			self.args=atomic.args
	def getFirst(self):
		atomic=Atomic("",[])
		res=VCLC(atomic) 
		res.args.append(self.args[0])
		
		return res
	
	def getRest(self):
		atomic=Atomic("",[])
		res=VCLC(atomic) 
		res.args=(self.args[1:])
		
		return res
	
	def  getOp(self):
		res=VCLC()
		res.op=self.op
		return res
	def getArgs(self):
		res=VCLC()
		res.args=list(self.args)
		return res

class Unifier(object):
	"""docstring for Unifier"""
	timeStamp=0
	occur_map={}
	
	def __init__(self):
		self.timeStamp=0
		self.occur_map={}
	
	def unify_var(self,var,x,sub):
		self.timeStamp+=1
		if var in sub.mapping:					# if {var/val} ∈ θ then return UNIFY(val,x,θ) 
			atomic1=Atomic("",[])
			z=VCLC(atomic1)
			atomic2=Atomic("",[])
			w=VCLC(atomic2)
			z.args.append(sub.mapping[var])
			w.args.append(x)
			self.occur_map[var+":"+x]=self.timeStamp
			sub=self.unify(z,w,sub)
			del self.occur_map[var+":"+x]
		elif x in sub.mapping:  				# else if {x/val} ∈ θ then return UNIFY(var,val,θ)
			atomic1=Atomic("",[])
			z=VCLC(atomic1)
			atomic2=Atomic("",[])
			w=VCLC(atomic2)
			z.args.append(var)		
			w.args.append(sub.mapping[x])
			self.occur_map[var+":"+x]=self.timeStamp
			sub=self.unify(z,w,sub)
			del self.occur_map[var+":"+x]
		elif (var+":"+x) in self.occur_map and self.occur_map[var+":"+x]>=sub.timeStamp:		# else if OCCUR-CHECK?(var,x) then return failure 
			sub.isFail=True
		else:							# else return add {var /x } to θ
			newsub=sub.add(var,x);
			newsub.timeStamp=self.timeStamp
			return newsub
		return sub

	def unify(self,x,y,sub):
		if sub.isFail:					# if θ = failure then return failure
			return sub
		if cmp(x.args,y.args)==0  and x.op==y.op:	# else if x = y then return θ
			return sub
		elif isVar(x) and (not isList(y)) and (not isComp(y)):		# else if VARIABLE?(x) then return UNIFY-VAR(x,y,θ)
			return self.unify_var(x.args[0],y.args[0],sub)
		elif isVar(y) and not isList(x) and not isComp(x):		# else if VARIABLE?(y) then return UNIFY-VAR(y,x,θ)
			return self.unify_var(y.args[0],x.args[0],sub)
		elif isComp(x) and isComp(y):	# else if COMPOUND?(x) and COMPOUND?(y) then return UNIFY(x .ARGS, y.ARGS, UNIFY(x .OP, y.OP, θ)) 
			return self.unify(x.getArgs(),y.getArgs(),self.unify(x.getOp(),y.getOp(),sub))
		elif isList(x) and isList(y):	# else if LIST?(x) and LIST?(y) then return UNIFY(x.REST,y.REST,UNIFY(x.FIRST,y.FIRST,θ)) 
			res=self.unify(x.getFirst(),y.getFirst(),sub)
			return self.unify(x.getRest(),y.getRest(),res)
		else:							# else return failure 
			sub.isFail=True
			return sub


class Occur(object):	#store the occurred atomics to improve efficiency and avoid infinite loop
	"""docstring for Occur"""
	lf=[] #list<pair<fact,int>>
	def find(self,atomic):
		for arg in atomic.args:
			if arg[0].islower():
				return False
		for arg in self.lf:
			if atomic==arg[0] and arg[1]==0:
				return 1
			if atomic==arg[0] and arg[1]==1:
				return 2
		return 0

	def add(self,atomic):
		for arg in atomic.args:
			if arg[0].islower():
				return
		pair=[atomic,0]
		self.lf.append(pair)
			
	def alter(self,atomic):
		for arg in self.lf:
			if atomic==arg[0]:
				arg[1]=1										
						
class BackwardChaining(object):
	"""docstring for BackwardChaining"""
	timeStamp=0
	uni=Unifier()
	occ=Occur()
	
	def __init__(self):
		super(BackwardChaining, self).__init__()
		timeStamp=0
	
	def getBCFirst(self,atomics):
		return atomics[0]
	
	def getBCRest(self,atomics):
		res=atomics[1:]
		return res

	def stand(self,lhs,rhs,nlhs,nrhs): 					# STANDARDIZE-VARIABLES((lhs, rhs))
		for atomic in lhs:
			for i in range(len(atomic.args)):
				tmpAtom=Atomic("",[])
				tmpAtom.args=atomic.args
				tmpAtom.op=atomic.op
				if atomic.args[i][0].islower() :
					tmpAtom.args[i]=atomic.args[i]+":"+str(self.timeStamp)
				nlhs.append(tmpAtom)
		
		nrhs.args=rhs.args
		nrhs.op=rhs.op
		for i in range(len(rhs.args)):
			if rhs.args[i][0].islower() :
				nrhs.args[i]=nrhs.args[i]+":"+str(self.timeStamp)
		
	def subst(self,sub,first):				# SUBST(θ, first)
		res=Atomic("",[])
		res.args=list(first.args)
		res.op=first.op
		for i in range(len(res.args)):
			if res.args[i] in sub.mapping:
				res.args[i]=sub.mapping[res.args[i]]
		return res

	def fetch_rule(self,kb,goal):			# FETCH-RULES-FOR-GOAL(KB, goal)
		rules=[]
		for cla in kb:
			if cla.conclusion.op==goal.op:
				rules.append(cla)
		
		return rules

	def bc_or(self,kb,goal,sub):					# generator FOL-BC-OR(KB,goal,θ) yields a substitution
		result=[]
		tmp=self.subst(sub,goal)
		res=self.occ.find(tmp)
		if res==1:
			sub.isFail=True
			result.append(sub)
			printFile(tmp,"Ask")
			printFile(tmp,"False")
			return
		if res==2:
			printFile(tmp,"Ask")
			result.append(sub)
			printFile(tmp,"True")
			yield sub
		self.occ.add(tmp)
		self.timeStamp+=1
		rules=self.fetch_rule(kb,goal)
		point=0
		hasFind=False
		for rule in rules:	# for each rule (lhs ⇒ rhs) in FETCH-RULES-FOR-GOAL(KB, goal) do
			if len(rule.atomicList)==0:
				tag=True	
				for i in range(len(goal.args)):
					if goal.args[i][0].isupper() and rule.conclusion.args[i][0].isupper():
						if goal.args[i]!=rule.conclusion.args[i]:
							tag=False
							break
				if tag==False:
					if point==len(rules)-1 and not hasFind:
						printFile(tmp,"Ask")
						break
					point+=1
					continue
						
			printFile(tmp,"Ask")
			sub.isFail=False

			lhs=rule.atomicList
			rhs=rule.conclusion
			nlhs=[]
			nrhs=Atomic("",[])
			self.stand(lhs,rhs,nlhs,nrhs)					# (lhs, rhs) ← STANDARDIZE-VARIABLES((lhs, rhs))
			rhsn=VCLC(nrhs)
			goaln=VCLC(goal)
			uni_res=self.uni.unify(rhsn,goaln,sub)
			if uni_res.isFail:
				point+=1
				continue
			
			for newSub in self.bc_and(kb,lhs,uni_res):			# for each θ′ in FOL-BC-AND(KB,lhs,UNIFY(rhs, goal, θ)) do
				if not newSub.isFail:
					hasFind=True
					tmpA=self.subst(newSub,tmp)
					printFile(tmpA,"True")
					self.occ.alter(tmp)
					result.append(newSub)							# 			yield θ′
					yield newSub
			point+=1
		if len(rules)==0:
			printFile(tmp,"Ask")
			# printFile(tmp,"False")
			
		if len(result)==0:
			printFile(tmp,"False")
			for a in goal.args:
				if a in sub.mapping:
					del sub.mapping[a]
		return

	def bc_and(self,kb,goal,sub):			# generator FOL-BC-AND(KB,goals,θ) yields a substitution
		result=[]
		if sub.isFail:					# if θ = failure then return
			return
		elif len(goal)==0:				# else if LENGTH(goals) = 0 then yield θ
			result.append(sub)
			yield sub
		else:
			fir=self.getBCFirst(goal)			# first,rest ← FIRST(goals), REST(goals)
			res=self.getBCRest(goal)			
			for newSub in self.bc_or(kb,self.subst(sub,fir),sub):		# for each θ′ in FOL-BC-OR(KB, SUBST(θ, first), θ) do
				for newnewSub in self.bc_and(kb,res,newSub):		# for each θ′′ in FOL-BC-AND(KB,rest,θ′) do 
					if not newnewSub.isFail:
						result.append(newnewSub)		
						yield newnewSub								# yield θ′′
			if len(result)==0:
				for x in goal:
					for a in x.args:
						if a in sub.mapping:
							del sub.mapping[a]
			return

######################## end structure ######################

######################## assist implementation ######################
def  dealAtomix(atomic):		# translate line into object Atomic
	funcName=atomic[0:atomic.index("(")].strip()
	args=atomic[atomic.index("(")+1: atomic.index(")")].split(", ")
	tmp=Atomic(funcName,args)
	return tmp

def initTarget(line):
	atomics=line.split(" && ")
	for atomic in atomics:
		targets.append(dealAtomix(atomic))

def initClause(line,n):
	atomicList=[]
	num=0
	f=line.find(" => ")
	if f>=0:
		atomics=line[0:f].split(" && ")
		for atomic in atomics:
			atomicList.append(dealAtomix(atomic))
		conclusion=dealAtomix(line[f+3:])
	else:
		atomicList=[]
		conclusion=dealAtomix(line)
	clause=Clause(atomicList,conclusion,n)
	clauses.append(clause)

def printFile(atomic,tag,isEnd=False):
	global output
	if atomic :
		outstr=tag+": "+atomic.op+"("
		for i in range(len(atomic.args)):
			if i>0:
				outstr+=", "
			if atomic.args[i][0].islower():
				outstr+="_"
			else:
				outstr+=atomic.args[i]
		outstr+=")\n"
		output.write(outstr)
	else:
		if isEnd:
			output.write(tag)
		else:
			output.write(tag+"\n")

def isComp(x):						# COMPOUND?(x) 
	return x.op!=""

def isList(x):						# LIST?(x)
	if (not isComp(x)) and len(x.args)>1:
		return True
	return False

def isConstant(x):					# CONSTANT?(x)
	if (not isComp(x)) and x.args[0][0].isupper():
		return True
	return False

def isVar(x):						# VARIABLE?(x)
	if (not isComp(x)) and (not isList(x)) and x.args[0][0].islower():
		return True
	return False

def occur_check(var,x):				# OCCUR-CHECK?(var,x)
	if type(Atomic())==type(x):
		for arg in x.args:
			if arg.find("(")>=0 and arg.find(var)>=0:
				return True
	return False
	
######################## end implementation ######################						





####################### main function ####################
fileName=""
# output=open("output.txt","w+")
if sys.argv[1]=="-i":
	fileName=sys.argv[2]
else:
	sys.exit()
apd=fileName.split("_")
output=open("testCases/myoutput_"+apd[1],"w+")
input_file = open(fileName)
count =len(open(fileName).readlines())

i=0
clauses=[]
targets=[]
clauseNum=0
subsut={}
for line in input_file:
	if(i==0):
		initTarget(line.strip())
	elif(i==1):
		clauseNum=int(line.strip())
	else:
		initClause(line.strip(),i-2)
	i+=1
	
final=False
for i in range(len(targets)):
	tar=targets[i]
	bc=BackwardChaining()
	sub=Substitution()
	t=False
	for res in bc.bc_or(clauses,tar,sub):
		if not res.isFail:
			t=True
			break
	if t==False:
		printFile(None,"False",True)
		break
	else:
		if i==len(targets)-1:
			printFile(None,"True",True)
	
output.close()

		





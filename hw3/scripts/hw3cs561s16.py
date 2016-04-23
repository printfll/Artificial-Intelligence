# -*- coding: utf-8 -*-
import sys
import copy
import os
from collections import OrderedDict
######################## structure ######################
class Dist(object):
	"""docstring for Dist"""
	prob={}
	name=""
	values=[]
	def __init__(self, name):
		self.name = name
		self.values=[]
		self.prob={}
	
	def __getitem__(self,val):
		if val in self.prob:
			return self.prob[val]
		else:
			return 0

	def __setitem__(self,val,p):
		if val not in self.values:
			self.values.append(val)
		self.prob[val]=p

	def normalize(self):
		# print "dist:",self.name
		total=sum(self.prob.values())
		if total>1.1 or total<0.9:
			for val in self.prob:
				self.prob[val]/=total
		return self

class Target(object):
	"""docstring for Target"""
	typ=""	#type of target: P, EU, MEU
	pre={}	#node name before |
	pro={}	#node name after |
	def __init__(self, line):
		self.pre=OrderedDict()
		self.pro={}
		if line=="":
			self.typ=""
			return
		self.typ=line[0]
		tmp=line.split("(")[1]
			
		content=tmp[0:len(tmp)-1]
		seg=content.split("|")
		preC=seg[0].split(",")
		for i in range(len(preC)):
			x=preC[i]
			preMap={}
			atomic=x.split("=")
			preName=atomic[0].strip()
			if len(atomic)>1:
				if atomic[1].strip()=="+":
					self.pre[preName]=True
				else:
					self.pre[preName]=False
			else:
				self.pre[preName]=-1
		if len(seg)>1:
			proC=seg[1].split(",")
			for x in proC:
				proMap={}
				atomic=x.split("=")
				proName=atomic[0].strip()
				if len(atomic)>1:		
					if atomic[1].strip()=="+":
						self.pro[proName]=True
					else:
						self.pro[proName]=False
				else:
					self.pro[proName]=-1

def printTar(tar):
	print "target:",tar.typ,"(",tar.pre,"|",tar.pro,")"
		
class Node(object):
	"""docstring for Node"""
	name=""
	parents=[]
	children=[]
	cpt={}
	isDeci=False
	def __init__(self, n):
		self.children=[]
		self.parents=[]
		self.cpt={}
		self.name=""
		if n=="":
			return
		ns=n.split("|")
		self.name = ns[0].strip()
		if len(ns)>1:
			self.parents=ns[1].strip().split(" ")
				
	def addCond(self,cond):
		items=cond.split(" ")
		prior=[]
		for x in xrange(1,len(items)):
			if items[x]=="+":
				prior.append(True)
			else:
				prior.append(False)
		self.cpt[tuple(prior)]=(float)(items[0])

	def p(self,value,e):
		key=EVENT_VALUE(e,self.parents)
		# print "p: key:",key,", node name:",self.name,",self cpt:",self.cpt
		if self.cpt=={} or len(self.cpt)==0:
			ptrue=1
		else:
			ptrue=self.cpt[key]
		# print "p ptrue:",ptrue
		if value==True:
			return ptrue
		else:
			return 1-ptrue

class Net(object):
	"""docstring for Net"""
	nodes=[]
	variables=[]

	def __init__(self):
		super(Net, self).__init__()
		self.nodes=[]
		self.variables=[]
	
	def addNode(self,node):
		self.nodes.append(node)
		self.variables.append(node.name)
		for par in node.parents:
			self.findNode(par).children.append(node)

	def findNode(self,var):
		for n in self.nodes:
			if n.name==var:
				return n	
		print "can't findNode:",var
	
	def findValue(self):		
		return [True,False]

def printNode(n):
	print "node:",n.name,"|",n.parents,n.cpt
			
class Utility(object):
	"""docstring for Utility"""
	dependency=[]		#name of node
	utCondList={}		#utility of node
	def __init__(self, n):
		super(Utility, self).__init__()
		self.dependency=[]
		self.utCondList={}
		self.dependency=n.split("|")[1].strip().split(" ")
	def addUtilityCond(self,line):
		items=line.split(" ")
		prior=[]
		
		for x in xrange(1,len(items)):
			if items[x]=="+":
				prior.append(True)
			else:
				prior.append(False)
		self.utCondList[tuple(prior)]=	(float)(items[0])

def printUti(ut):
	print "ut:",ut.dependency,ut.utCondList
		
####################### end structure ###################

#######################  function    ###################
def extend(e,var,val):
    tar = e.copy()
    tar[var] = val
    return tar

def EVENT_VALUE(e,variables):
	# print "EVENT_VALUE:", e
	if isinstance(e,tuple) and len(e)==len(variables):
		return e
	else:
		tu=tuple([e[var]for var in variables])
		return tu

def ENUMERATION_ASK(X,e,bn):	# function ENUMERATION-ASK(X , e, bn) returns a distribution over X 
	# print"ENUMERATION_ASK:",X,",e:",e
	Q=Dist(X)					# Q(X ) ← a distribution over X , initially empty
	for xi in bn.findValue():	# for each value xi of X do
		Q[xi]=ENUMERATE_ALL(bn.variables,extend(e,X,xi),bn)	# 	Q(xi) ← ENUMERATE-ALL(bn.VARS, exi),where exi is e extended with X = xi
		# print "Q[xi]:",Q[xi]
	return Q.normalize()		# return NORMALIZE(Q(X))
	
def ENUMERATE_ALL(variables,e,bn):	# function ENUMERATE-ALL(vars, e) returns a real number 
	# print "ENUMERATE_ALL:",variables
	if not variables:			# if EMPTY?(vars) then return 1.0
		return 1.0			
	Y,rest=variables[0],variables[1:]	# Y ← FIRST(vars)
	Ynode=bn.findNode(Y)
	if Y in e:				# if Y has value y in e
		return Ynode.p(e[Y],e)*ENUMERATE_ALL(rest,e,bn)		# 	then return P (y | parents(Y )) × ENUMERATE-ALL(REST(vars), e) 
	else:					# else return􏰂 Sum y P(y|parents(Y)) × ENUMERATE-ALL(REST(vars),ey) where ey is e extended with Y = y
		return sum(Ynode.p(y,e)*ENUMERATE_ALL(rest,extend(e,Y,y),bn)
			for y in bn.findValue())

def copyNode(src,tar):
	tar.name=src.name
	tar.parents=src.parents[:]	
	tar.cpt=src.cpt	
	tar.isDeci=src.isDeci
	return tar

def copyTar(src,tar):
	tar.typ=src.typ
	tar.pre=src.pre.copy()
	tar.pro=src.pro.copy()
	return tar

def writeFile(line,isEnd):
	global output
	if not isEnd:
		output.write(line+"\n")
	else:
		output.write(line)

def calSingleProb(tar):
	# print "calSingleProb tar:",printTar(tar)
	item=list(tar.pre.keys())
	# print "calSingleProb: item0:",item[0],",t.pro:",tar.pro
	res=ENUMERATION_ASK(item[0],tar.pro,net)
	return res

def calProb(tar):
	# print "calProb:",printTar(tar)
	if (len(tar.pre)>1 and len(tar.pro)==0)  :	#P(A, B, C, D)=P(A|B,C,D)*P(B,C,D)
		tmp=Target("")
		tmpList=[]
		tmp=copyTar(tar,tmp)
		res=1.0
		while len(tmp.pre)>=1:
			single=Target("")
			preList=list(tmp.pre.keys())
			fir=preList[0]
			single.pre={fir:tmp.pre[fir]}
			del tmp.pre[fir]
			single.pro=tmp.pre.copy()
			tmpList.append(single)
		# print "calProb tmpList:",
		for t in tmpList:
			# print "calProb: t.pre:",t.pre,",t.pro:",t.pro
			tmpres= calSingleProb(t)
			# print "calSingleProb:",tmpres.prob
			item=(list(t.pre.keys()))
			resnum=tmpres.prob[t.pre[item[0]]]
			res*=resnum
	elif len(tar.pre)>1 and len(tar.pro)>=1:	#P(A, B, C |D, E)=P(A,B,C,D,E)/P(D,E)
		multiTmp=Target("")
		multiTmp.pre=tar.pre.copy()
		multiTmp.pre.update(tar.pro.copy())
		multiTmp.pro={}
		div1=calProb(multiTmp)
		multiTmp2=Target("")
		multiTmp2.pre=tar.pro.copy()
		multiTmp2.pro={}
		div2=calProb(multiTmp2)
		res=(1.0*div1)/div2
	elif (len(tar.pre)==1):	#P(A|B, C)
		tmpres=calSingleProb(tar)
		item=(list(tar.pre.keys()))
		res=tmpres.prob[tar.pre[item[0]]]

	# print "calProb res:",res
	return res

def calEU(tar):
	# EU(I)=sum(P(D|I)*U(D))
	# EU(I|L)=sum(P(D|I,L)*U(D))
	probTar=Target("")
	probPreList={}
	probProList=tar.pre.copy()
	probProList.update(tar.pro.copy())
	for var in utTable.dependency:
		n=net.findNode(var)
		if not n.isDeci and var not in probProList:
			probPreList[var]=tuple([True,False])
	probTar.pre=probPreList
	probTar.pro=probProList
	probTar.typ="P"
	one_arg=[(True),(False)]
	two_arg=[(True,True),(True,False),(False,True),(False,False)]
	three_arg=[(True,True,True),(True,False,True),(False,True,True),(False,False,True),(True,True,False),(True,False,False),(False,True,False),(False,False,False)]
	length=len(probTar.pre)
	if length==1:
		args=one_arg
	elif length==2:
		args=two_arg
	elif length==3:
		args=three_arg
	result=0
	for x in args:
		point=0
		if length==1:
			item=list(probTar.pre.keys())
			probTar.pre[item[0]]=x
		else:
			for var in probTar.pre.keys():
				probTar.pre[var]=x[point]
				point+=1
		
		tmpProb=calProb(probTar)
		# print"before:",printTar(probTar)
		tmpUti=[]
		for y in utTable.dependency:
			if y in probTar.pre:
				tmpUti.append(probTar.pre[y])
			elif y in probTar.pro:
				tmpUti.append(probTar.pro[y])
			else:
				print "cannot find the dependency node:",y
		tmpUtiNum=utTable.utCondList[tuple(tmpUti)]
		result+=tmpUtiNum*tmpProb
		# print "calEU:",probTar.pre,",",probTar.pro,",tmpProb:",tmpProb,",tmpUtiNum:",tmpUtiNum,",result:",result,"\n----------\n\n "
	# print "result:",result,"\n----------\n\n"
	return result

def calMEU(tar):
	one_arg=[(True),(False)]
	two_arg=[(True,True),(True,False),(False,True),(False,False)]
	three_arg=[(True,True,True),(True,False,True),(False,True,True),(False,False,True),(True,True,False),(True,False,False),(False,True,False),(False,False,False)]
	length=len(tar.pre)
	if length==1:
		args=one_arg
	elif length==2:
		args=two_arg
	elif length==3:
		args=three_arg
	result={}
	for x in args:
		if length==1:
			item=list(tar.pre.keys())
			tar.pre[item[0]]=x
		else:
			point=0
			for var in tar.pre.keys():
				tar.pre[var]=x[point]
				point+=1
		
		tmpRes=calEU(tar)

		result[x]=tmpRes
	# print "calMEU:",tar.pre,",tar.pro:",tar.pro,"result:",result
	maxRes={}
	maxKey=None
	maxNum=-1000000000000000
	for (k,value) in result.items():
		if value>maxNum:
			maxKey=k
			maxNum=value
			# print "maxKey:",maxKey
		
	maxRes["key"]=maxKey
	maxRes["num"]=maxNum
	# print "maxRes:",maxRes
	return maxRes


####################### end function ###################

####################### main function ####################
fileName=""
output=open("output.txt","w+")
if sys.argv[1]=="-i":
	fileName=sys.argv[2]
else:
	sys.exit()

input_file = open(fileName)
count =len(open(fileName).readlines())

i=0
targetList=[]
probabilityList=[]
decisionList=[]
readTag=0	#0: read target, 1: read probability, 2: read utility table
tmpNode=None
utTable=None
net=Net()
for line in input_file:
	# print "line:",line
	line=line.strip()
	
	if readTag==0: 
		if line=="******" :
			readTag=1
		else:
			newT=Target("")
			targetList.append(copyTar(Target(line),newT))
			
	elif readTag==1:
		if line[0].isupper():
			tmpNode=Node(line)
		elif line[0].isdigit():
			tmpNode.addCond(line)
		elif line=="decision":
			newDNode=Node("")
			tmpNode.cpt={():0.5}
			tmpNode.isDeci=True
			decisionList.append(copyNode(tmpNode,newDNode))
			net.addNode(newDNode)
			tmpNode=None
		elif line=="***" or line=="******":
			if  tmpNode != None:
				newNode=Node("")
				probabilityList.append(copyNode(tmpNode,newNode))
				net.addNode(newNode)
				tmpNode=None
			if line=="******":
				readTag=2
	elif readTag==2:
		if line[0].islower():
			utTable=Utility(line)
		else:
			utTable.addUtilityCond(line)
if tmpNode!=None and readTag==1:
	newNode=Node("")
	probabilityList.append(copyNode(tmpNode,newNode))
	net.addNode(newNode)
	tmpNode=None

# print "bey's net:"print net.variables
output=open("output.txt","w+")
offset=1e-8
for i in range(len(targetList)):
	resStr=""
	t=targetList[i]
	# printTar(t)
	if i==len(targetList)-1:
		isEnd=True
	else:
		isEnd=False
	
	if t.typ=="P":
		tmp=calProb(t)+offset
		resStr= str("%.2f" % tmp)
	elif t.typ=="E":
		tmp=calEU(t)+offset
		resStr=str(int(round(tmp,0)))
	elif t.typ=="M":
		res=calMEU(t)
		domain=res["key"]
		if isinstance(domain,bool):
			if domain:
				resStr+="+ "
			else:
				resStr+="- "
		elif isinstance(domain,tuple):
			for v in domain:
				if v:
					resStr+="+ "
				else:
					resStr+="- "
		r=int(round(res["num"]+offset))
		resStr+=str(r)
	writeFile(resStr,isEnd)
	# print "result:",resStr
	# print "---------------"
output.close()
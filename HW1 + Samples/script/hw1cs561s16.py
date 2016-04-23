# -*- coding: utf-8 -*-
import sys
import copy
import os

########## first part init implementation #############
def initAlg(line):
	global algType
	algType=int(line)		
	
def initPlayer(line):
	global player
	player=line
	
def initCutOff(line):
	global cutoff
	cutoff=int(line)
########## end first part init #############



########## second part init implementation ##############
def initBattle(line):
	global battle
	battle=int(line)

def initFirPlayer(line):
	global firPlayer
	firPlayer=line

def initFirAlg(line):
	global firAlgType
	firAlgType=int(line)

def initFirCutOff(line):
	global firCutOff
	firCutOff=int(line)

def initSecPlayer(line):
	global secPlayer
	secPlayer=line

def initSecAlg(line):
	global secAlgType	
	secAlgType=int(line)

def initSecCutOff(line):
	global secCutOff
	secCutOff=int(line)
	
########## end second part init #############

def initBoard(line): #init the value 
	global board
	global i
	global count
	pointer=0
	if count==13:
		offset=4
	elif count==17:
		offset=8
	
	arr=line.split(" ")
	for val in arr:
		board[i-offset][pointer]=int(val)
		pointer+=1

def initState(line): #init the state
	global state
	global i
	global count
	pointer=0
	if count==13:
		offset=9
	elif count==17:
		offset=13

	for c in line:
		state[i-offset][pointer]=c
		pointer+=1	

def getScore(state): #compute current score
	global board
	global player
	score=0
	if player=="O":
		opp="X"
	else:
		opp="O"

	for i in range(5):
		for j in range(5):
			if state[i][j]==player:
				score+=board[i][j]
			elif state[i][j]==opp:
				score-=board[i][j]
	return score
	
def checkNei(state,i,j,tag=True):  #check if any adjacent node on the same side 
	global player
	if tag:
		nowPlay=player
	else:
		if player=="X":
			nowPlay="O"
		else:
			nowPlay="X"
	moveX=[0,0,1,-1]
	moveY=[1,-1,0,0]
	for ox in range(4):
		newX=i+moveX[ox]
		newY=j+moveY[ox]
		if newX<0 or newX>=5 or newY<0 or newY>=5:
			continue
		elif state[newX][newY]==nowPlay:
			return True
	
	return False

def canMove(state): #check if the board is full
	for line in state:
		for item in line:
			if item=="*":
				return True
	return False
	
def move(state,x,y,tag=True): #move at [x,y], true: we move, False: opponent move
	global player
	
	if not tag:
		if player=="X":
			nowPlay="O"
		else:
			nowPlay="X"
	else:
		nowPlay=player
	moveX=[0,0,1,-1]
	moveY=[1,-1,0,0]
	movePos= [[-1 for col in range(2)] for row in range(4)]
	
	movePos[0][0]=x
	movePos[0][1]=y
	state[x][y]=nowPlay
	point=1
	if checkNei(state,x,y,tag):  #only having existing neighbor can raid opposite
		for ox in range(4):
			newX=x+moveX[ox]
			newY=y+moveY[ox]
			if newX<0 or newX>=5 or newY<0 or newY>=5:
				continue
			if state[newX][newY]!="*" and state[newX][newY]!=nowPlay : #opposite state
				movePos[point][0]=newX
				movePos[point][1]=newY
				point+=1
				state[newX][newY]=nowPlay

	return movePos

def undoMove(movePos): #undo the previous move
	global state
	global player
	state[movePos[0][0]][movePos[0][1]]="*"
	if player=="X":
		opp="O"
	else:
		opp="X"
	
	for x in range(1,3):
		if movePos[x][0]>-1:
			state[movePos[x][0]][movePos[x][1]]=opp
	

def GBFS(): #Greedy Best First Alg
	global state
	global player
	movePos= [[-1 for col in range(2)] for row in range(4)]#store changed opposite positions, at most change 3 opposite
	maxV=-sys.maxint-1

	for i in range(5):
		for j in range(5):
			if state[i][j]=="*" : #vacant state
				poss=move(state,i,j)
				tmp=getScore(state)
				undoMove(poss)
				if(tmp>maxV):
					movePos=poss
					maxV=tmp
																
	return movePos

def MinMax(state,d): #MiniMax Alg
	global column
	if cutoffTest(state,d):
		return getScore(state);
	v=-sys.maxint-1
	traverse_file.write ("Node,Depth,Value\n")

	action=[[-1 for col in range(2)] for row in range(4)]
	poss=[[-1 for col in range(2)] for row in range(4)]
	for i in range(5):
		for j in range(5):
			if state[i][j]=="*" : #vacant state
				newState=copy.deepcopy(state)
				printMM(-1,-1,d,v)
				poss=move(newState,i,j)
				
				val=MIN_VALUE(newState,d+1,i,j)
				if v<val:
					v=val
					action=poss
	
	printMM(-1,-1,d,v,True)
	return action

def MAX_VALUE(state,d,posx,posy): #implementation of MAX
	global column
	if cutoffTest(state,d):
		score=getScore(state)
		printMM(posx,posy,d,score)
		return score;
	v=-sys.maxint-1
	for i in range(5):
		for j in range(5):
			if state[i][j]=="*" : #vacant state
				newState=copy.deepcopy(state)
				printMM(posx,posy,d,v)
				poss=move(newState,i,j)
				val=MIN_VALUE(newState,d+1,i,j)
				v=max(v,val)
				
	printMM(posx,posy,d,v)
	return v

def MIN_VALUE(state,d,posx,posy): #implementation of MIN
	global column	
	if cutoffTest(state,d):
		score=getScore(state)
		printMM(posx,posy,d,score)
		return score;
	v=sys.maxint
	for i in range(5):
		for j in range(5):
			if state[i][j]=="*" : #vacant state
				newState=copy.deepcopy(state)
				printMM(posx,posy,d,v)
				poss=move(newState,i,j,False)
				val=MAX_VALUE(newState,d+1,i,j)
				v=min(v,val)
	
	printMM(posx,posy,d,v)			
	return v
				
def AlphaBeta(state,d): #Alpha_Beta Pruning Alg
	
	global column
	if cutoffTest(state,d):
		return getScore(state);
	v=-sys.maxint-1

	action=[[-1 for col in range(2)] for row in range(4)]
	poss=[[-1 for col in range(2)] for row in range(4)]
	alpha=-sys.maxint-1
	beta=sys.maxint
	traverse_file.write( "Node,Depth,Value,Alpha,Beta\n")
	for i in range(5):
		for j in range(5):
			if state[i][j]=="*" : #vacant state
				newState=copy.deepcopy(state)
				printAB(-1,-1,d,v,alpha,beta)
				poss=move(newState,i,j)
				
				val=MIN_VALUE_BETA(newState,d+1,alpha,beta,i,j)
				if v<val:
					v=val
					action=poss
				
				
				if v>=beta:
					printAB(-1,-1,d,v,alpha,beta,True)
					return v
				alpha=max(alpha,v)
	printAB(-1,-1,d,v,alpha,beta,True)
	return action
	

def MAX_VALUE_ALPHA(state,d,alpha,beta,posx,posy): #Implementation of MAX_ALPHABETA
	global column
	if cutoffTest(state,d):
		score=getScore(state)
		printAB(posx,posy,d,score,alpha,beta)
		return score;
	v=-sys.maxint-1
	for i in range(5):
		for j in range(5):
			if state[i][j]=="*" : #vacant state
				# printAB(posx,posy,d,v,alpha,beta)

				newState=copy.deepcopy(state)
				printAB(posx,posy,d,v,alpha,beta)
				poss=move(newState,i,j)
				
				val=MIN_VALUE_BETA(newState,d+1,alpha,beta,i,j)
				v=max(v,val)
				
				if v>=beta:
					printAB(posx,posy,d,v,alpha,beta)
					return v
				alpha=max(alpha,v)
	printAB(posx,posy,d,v,alpha,beta)
	return v

def MIN_VALUE_BETA(state,d,alpha,beta,posx,posy): #Implementation of MIN_ALPHABETA
	global column	
	if cutoffTest(state,d):
		score=getScore(state)
		printAB(posx,posy,d,score,alpha,beta)
		return score;
	v=sys.maxint
	for i in range(5):
		for j in range(5):
			if state[i][j]=="*" : #vacant state
				
				newState=copy.deepcopy(state)
				printAB(posx,posy,d,v,alpha,beta)
				
				poss=move(newState,i,j,False)
				val=MAX_VALUE_ALPHA(newState,d+1,alpha,beta,i,j)
				v=min(v,val)
				if v<=alpha:
					printAB(posx,posy,d,v,alpha,beta)
					return v
				beta=min(beta,v)
	printAB(posx,posy,d,v,alpha,beta)		
	return v

def cutoffTest(state,d): #check if reach the cutoff depth
	global cutoff
	if d>= cutoff or not canMove(state):
		return True
	else:
		return False

def printMM(i,j,d,v,isLast=False): #write traverse_log of MINIMAX
	if i<0:
		pos="root"
	else:
		pos=column[j]+str(i+1)
	if v==-sys.maxint-1:
		val="-Infinity"
	elif v==sys.maxint:
		val="Infinity"
	else:
		val=str(v)

	string=pos+","+str(d)+","+val

	if not isLast:
		string+="\n"
	traverse_file.write(string)
	

def printAB(i,j,d,v,alpha,beta,isLast=False): #write traverse_log of ALPHA_BETA
	if i<0:
		pos="root"
	else:
		pos=column[j]+str(i+1)
	if v==-sys.maxint-1:
		val="-Infinity"
	elif v==sys.maxint:
		val="Infinity"
	else:
		val=str(v)

	if alpha==-sys.maxint-1:
		a="-Infinity"
	elif alpha==sys.maxint:
		a="Infinity"
	else:
		a=str(alpha)

	if beta==-sys.maxint-1:
		b="-Infinity"
	elif beta==sys.maxint:
		b="Infinity"
	else:
		b=str(beta)
	string=pos+","+str(d)+","+val+","+a+","+b
	if not isLast:
		string+="\n"
	traverse_file.write(string)
	


def WriteFile(ofile,state,step): #write board
	
	if step>1:
		ofile.write("\n")
	for i in range(5):
		for j in range(5):
			ofile.write(state[i][j])
			if j==4 and i<4:
				ofile.write("\n")
	

def makeAction(action): #execute the movement
	global state
	for row in action:
		if row[0]>-1:
			state[row[0]][row[1]]=player
		else:
			break

	
################## begin of the main ################	


	

fileName=""
if sys.argv[1]=="-i":
	fileName=sys.argv[2]
else:
	sys.exit()


input_file = open(fileName)
count =len(open(fileName).readlines())

output_file=open("next_state.txt","w+")
traverse_file=open("traverse_log.txt","w+")

rowCount=5 
column=["A","B","C","D","E"]
board= [[0 for col in range(rowCount)] for row in range(rowCount)] #line 4- line 8
state= [['*' for col in range(rowCount)] for row in range(rowCount)] #line 9- line 13
i=1

if count==13:
	######### Part 1 ###########	
	
	algType=-1 #line 1
	player=-1   #line 2
	cutoff=-1   #line 3
	dic={
		1:initAlg,2:initPlayer,3:initCutOff,
		4:initBoard,5:initBoard,6:initBoard,7:initBoard,8:initBoard,
		9:initState,10:initState,11:initState,12:initState,13:initState,
	}

	for line in input_file:
		dic[i](line.strip())
		i+=1

	if algType==1:
		action=GBFS()
	elif algType==2:
		action=MinMax(state,0)
	elif algType==3:
		action=AlphaBeta(state,0)

	makeAction(action)

	
	
	WriteFile(output_file,state,1)
	output_file.close
	traverse_file.close

elif count==17:
	####### part 2 #########
	battle=-1
	firPlayer=-1
	firAlgType=-1
	firCutOff=-1
	secPlayer=-1
	secAlgType=-1
	secCutOff=-1
	trace_file=open("trace_state.txt","w+")
	dic={
		1:initBattle,2:initFirPlayer,3:initFirAlg,4:initFirCutOff,5:initSecPlayer,6:initSecAlg,7:initSecCutOff,
		8:initBoard,9:initBoard,10:initBoard,11:initBoard,12:initBoard,
		13:initState,14:initState,15:initState,16:initState,17:initState,
	}

	for line in input_file:
		dic[i](line.strip())
		i+=1

	player=firPlayer
	algType=firAlgType
	cutoff=firCutOff
	step=1
	while canMove(state):
		if algType==1:
			action=GBFS()
		elif algType==2:
			action=MinMax(state,0)
		elif algType==3:
			action=AlphaBeta(state,0)
		makeAction(action)
		WriteFile(trace_file,state,step)
		step+=1
		if player==firPlayer:
			player=secPlayer
			algType=secAlgType
			cutoff=secCutOff
		else:
			player=firPlayer
			algType=firAlgType
			cutoff=firCutOff
	
	trace_file.close()
	
















# Copyright (c) Microsoft Corporation 2015

from z3 import *

import re
import string

set_param(proof=True)

t = Int('t')#time
t1 = Int('t1')#time
p = Int('p')#process id 
q = Int('q')#process id (sender)
q1=Int('q1')#process id (not sender/receiver)
pack = Int('pack')#packet id
pack1 = Int('pack1')#packet id 
T = Int('T')#period/interval


######################function declarations#######################
listen = Function('listen', IntSort(), IntSort(), BoolSort()) #takes two integers(time,process_id) as input, returns bool(listening or not)
transmit = Function('transmit', IntSort(), IntSort(), IntSort()) #takes two integers(time,process_id) as input, returns int(transmitting (garbage or packet) or not)
sleep = Function('sleep', IntSort(), IntSort(), BoolSort()) #takes two integers(time,process_id) as input, returns bool(sleeping or not)
knows = Function('knows', IntSort(), IntSort(), IntSort(), BoolSort()) #takes three integers(time,process_id,packet_id) as input, returns bool(knows packet or not)

#Solver() creates a general purpose solver.  
s = Solver()
s.reset()

#######################constraints###############################
constraint1a, constraint1,constraint2 = Bools('constraint1a constraint1 constraint2')
constraint4,constraint5,constraint6 = Bools('constraint4 constraint5 constraint6')
constraint7,constraint8,constraint9 = Bools('constraint7 constraint8 constraint9')
constraint10,constraint11,constraint12 = Bools('constraint10 constraint11 constraint12')
constraint13,constraint14a,constraint14b,constraint15 = Bools('constraint13 constraint14a constraint14b constraint15')
constraint16,constraint17a,constraint17b,constraint17c= Bools('constraint16 constraint17a constraint17b constraint17c')
constraint18a,constraint18= Bools('constraint18a constraint18')
constraint19,constraint20,constraint21 = Bools('constraint19 constraint20 constraint21')



#afunction for defining neighborship, e.g. a = neighbor(b) if a= b+1 or a = b-1

def neighbor(process1, process2):
    id_difference = process1-process2;
    if id_difference < 0:
        id_difference = id_difference * (-1);
    if id_difference == 1:
        print id_difference;
        return True;
    else:
        print id_difference;
        return False;



####Constraints can be added using the method add. We say the constraints have been asserted in the solver.####

s.add(Implies(constraint1a,T==5))
s.add(Implies(constraint1,
              And(t>=0,t<=4,
                  p>=0,p<=2,
                  q>=0,q<=2,
                  q1>=0,q1<=2,
                  pack>=0,pack<=2,                  
                  pack1>=0,pack1<=2
                  )))#restrict all integer variables(time,process ids,packet id, time intervals) to be positive

#a process at any time transmits garbage or packet or does not transmit at all
for t in range(0, 5):
    for p in range(0,3):
            s.add(Implies(constraint2,
                          Or(Exists(pack, And(pack>=0,pack<=2,transmit(t, p) == pack)),
                             transmit(t, p) == -1
                             )
                          )
                  )
            
#a process executes one action (transmit or listen or sleep) at a time
for t in range(0, 5):
    for p in range(0,3):
        s.add(Implies(constraint4,
                      Or(sleep(t,p)==True,
                         transmit(t,p)>=0,
                         listen(t,p)==True
                         ))
              )

#a process does exactly one action (transmit or listen or sleep) at a time
for t in range(0, 5):
    for p in range(0,3):
        s.add(Implies(constraint5,
                      And(Implies(sleep(t,p)==True,And((listen(t,p)==False),transmit(t,p)==-1)),
                          Implies(transmit(t,p)>=0,And((sleep(t,p)==False),(listen(t,p)==False))),
                          Implies(listen(t,p)==True,And((sleep(t,p)==False),transmit(t,p)==-1)))
                      ))
        
#Only process 0 knows all packets at time 0
for b in range(0, 3):
    s.add(Implies(constraint12,knows(0,0,b)==True))

#At time 0 all processes (>=0) know 0 that represents garbage
for p in range(1,3):
    s.add(Implies(constraint13,
                  Implies(t1<=0, knows(t1,p,0)==True))
          )


# at t=0, unaware of all packets
for p in range(1,3):
    for b in range(1, 3):
        print "Implies("+str(t1)+"<0,knows("+str(t1)+","+str(p)+","+str(b)+")==False)"
        s.add(Implies(constraint14a,ForAll(t1,Implies(t1<0,knows(t1,p,b)==False))))


for p in range(1,3):
    for b in range(1, 3):
        s.add(Implies(constraint14b,knows(0,p,b)==False))



#i transmit a packet I know= this is for processes > 0 # is it required?
#I know the packet that I am transmitting
for t in range(0, 4):
    for p in range(1,3):
        for b in range(1, 3):
            s.add(Implies(constraint15,
                          Implies(transmit(t,p)==b,knows(t-1,p,b)==True)
                          )
                  )
            
#Once I know a packet then I know it forever
#s.add(Implies(constraint16, ForAll((t,c,p,packet), Implies(knows(t,p,packet)==True,knows(t+c,p,packet)==True))))
for t in range(0, 4):
    for p in range(1,3):
        for b in range(0, 3):
            s.add(Implies(constraint16,
                          Implies(knows(t,p,b)==True,knows(t+1,p,b)==True)
                          ))
            

#one to one transmisssion
for t in range(0, 4):
    for p in range(1,3):
        for b in range(1, 3):
#            for q in range(0,p):
                s.add(Implies(constraint17a,              
                         Implies(And(knows(t+1,p,b) ==True, knows(t,p,b)==False),#if process p knows a packet now and did not know it in the previous step
                                 And(Exists(q,And(q>=0,q<p,transmit(t,q)== b)), listen(t,p)==True)
                                 )                     
                  )
          )
#one to one reception
for t in range(0, 4):
    for p in range(1,3):
        for b in range(1, 3):
#            for q in range(0,p):
                s.add(Implies(constraint17b,
                              Implies(And(knows(t,p,b)==False, listen(t,p)==True, Exists(q, And(q>=0,q<p,transmit(t,q)== b))),
                                      knows(t+1,p,b)==True
                                      )
                              )
                      )

'''
s.add(Implies(constraint17c,
              And(#transmit(0,0)==-1,
                  #transmit(1,0)==1,
                  #listen(1,1)==True,
                  #listen(1,2)==True,
                  #knows(2,1,1)==True,
                  #knows(2,2,1)==True,
                  #transmit(3,0)==2,
                  #listen(3,1)==True,
                  #listen(3,2)==True
                  )
              ))



              
#process p transmits a packet at time t+1 only if all processes know all previous packets at time t

s.add(Implies(constraint18,
              ForAll((p,pack),
                     Implies(And(transmit(t,p)==pack,t>=0,t<=3,p>=0,p<=2,pack>0,pack<=2),
                             ForAll((pack1,q), Implies(And(pack1<pack, q>0,q<=2, pack1>0),knows(t-1,q,pack1)==True))
                             )
                     )
              )
      )
'''

for t in range(0, 4):
    for p in range(0,3):
        for a in range(1, 3):
            for q in range(0, 3):
                for b in range(0,a):
                    print "Implies(transmit("+str(t)+","+str(p)+")=="+str(a)+",knows("+str(t-1)+","+str(q)+","+str(b)+")==True)"
                    s.add(Implies(constraint18,
                              Implies(transmit(t,p)==a,knows(t-1,q,b)==True)
                                  )
                          )

'''
#all processes eventually learn about all packets
s.add(Implies(constraint19,
              ForAll((pack,p),Implies(And(pack>0,pack<=2,p>=0,p<=2),knows(3,p,pack)==True))
              )
      )
'''
for p in range(0,3):
        for a in range(0, 3):
            #print 'knows(3,'+str(p)+','+str(a)+')==True'
            s.add(Implies(constraint19,knows(3,p,a)==True)
                  )

#The method check() solves the asserted constraints
satResult = s.check(#constraint1a,
                    constraint1,
                    constraint2,
                    constraint4,
                    constraint5,
                    #constraint6,constraint7,
                    #constraint8,constraint9,
                    #constraint10,constraint11,
                    constraint12,
                    constraint13,
                    constraint14a,
                    constraint14b,
                    constraint15,
                    constraint16,
                    constraint17a,constraint17b,
                    constraint18,
                    constraint19
                    )
print satResult


set_option(max_args=10000000, max_lines=1000000, max_depth=10000000, max_visited=1000000)

if (satResult == z3.unsat):
    #print s.statistics
    print s.unsat_core()
    #print s.proof()
else:
    print s.model()
    m=s.model()
    #print "f(x) =", m.evaluate(transmit(t,p)==2)

    f1=open('./modelfile', 'w+')
    model=str(s.model())
    f1.write(model)
    f1.close();

    f2=open('./transmitfile', 'w+')
    transmit_model=str(s.model()[transmit])
    f2.write(transmit_model)
    f2.close();

    f1=open('./modelfile', 'r+')
    f2=open('./transmitfile', 'r+')
    f3=open('./transmitfiledetailed', 'a+')

    f3.seek(0)
    f3.truncate()

    regex = re.compile(r'[\w]+\![\w]+') 

    lines = f2. readlines() #for each line in the transmit model file
    for line in lines:      
        words = regex.findall(line) #find if there are values to be replaced
        for word in words:          # for each such value find their equivalent from the full model file
            search_word = word + ' ='
            if search_word in model:
                equivalent_value = ((model.split(search_word))[1].split(']'))[0]
                equivalent_value = equivalent_value +'],'
                #print word
                #print equivalent_value
                #f3.write((model.split(search_word))[1].split(']')[0])
                if word in line:
                    line= string.replace(line,word,equivalent_value,1)
                    #print line
        f3.write(line)
    f3.close();
        





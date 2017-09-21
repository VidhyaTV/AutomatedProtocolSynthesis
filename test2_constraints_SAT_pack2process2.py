# Copyright (c) Microsoft Corporation 2015

from z3 import *

t = Int('t')#time
p = Int('p')#process id 
q = Int('q')#process id (sender)
q1=Int('q1')#process id (not sender/receiver)
pack = Int('pack')#packet id
pack1 = Int('pack1')#packet id 
T = Int('T')#period/interval

#create a datatype called transmission_content that can have only one of the following three values
transmission_content = Datatype('transmission_content')
transmission_content.declare('garbage')
transmission_content.declare('packet')
transmission_content.declare('not_transmitting')
transmission_content = transmission_content.create()

#variable of type transmission_content
trans = Const('trans', transmission_content)

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
constraint13,constraint14,constraint14a,constraint15 = Bools('constraint13 constraint14 constraint14a constraint15')
constraint16,constraint17= Bools('constraint16 constraint17')
constraint18a,constraint18= Bools('constraint18a constraint18')
constraint19,constraint20,constraint21 = Bools('constraint19 constraint20 constraint21')

####Constraints can be added using the method add. We say the constraints have been asserted in the solver.####

s.add(Implies(constraint1a,T==5))
s.add(Implies(constraint1,
              And(t>=0,t<=15,
                  p>=0,p<=1,
                  q>=0,q<=1,
                  q1>=0,q1<=1,
                  pack>=0,pack<=2,                  
                  pack1>=0,pack1<=2
                  )))#restrict all integer variables(time,process ids,packet id, time intervals) to be positive

#a process at any time transmits garbage or packet or does not transmit at all
s.add(Implies(constraint2,
              ForAll((t,p),
                     Implies(And(t>=0,t<=15,p>=0,p<=1,pack>=0,pack<=2),
                             Or(And(transmit(t, p) == pack,pack>0,pack<=2),
                                    transmit(t, p) == 0,
                                    transmit(t, p) == -1)
                             )
                     )
              )
      )

#a process executes one action (transmit or listen or sleep) at a time
s.add(Implies(constraint4,
              ForAll((p,t),
                     Implies(And(t>=0,t<=15,p>=0,p<=1),
                             Or(sleep(t,p)==True,
                                transmit(t,p)>=0,
                                listen(t,p)==True
                                ))))
      )

#a process does exactly one action (transmit or listen or sleep) at a time
s.add(Implies(constraint5,
              ForAll((p,t),
                     Implies(And(t>=0,t<=15,p>=0,p<=1),
                             And(Implies(sleep(t,p)==True,And((listen(t,p)==False),transmit(t,p)==-1)),
                                 Implies(transmit(t,p)>=0,And((sleep(t,p)==False),(listen(t,p)==False))),
                                 Implies(listen(t,p)==True,And((sleep(t,p)==False),transmit(t,p)==-1)))
                             ))))

#If process p is listening/not listening now(t) then it is listening/not listening after T(t+T)
s.add(Implies(constraint6,
              ForAll((p,t), Implies(And(t>=0,t<=15,p>=0,p<=1,listen(t,p)==True),listen(t+T,p)==True))))
s.add(Implies(constraint7,
              ForAll((p,t), Implies(And(t>=0,t<=15,p>=0,p<=1,listen(t,p)==False),listen(t+T,p)==False))))

#If process p is sleeping/not sleeping now(t) then it is sleeping/not sleeping after T(t+T)
s.add(Implies(constraint8,
              ForAll((p,t), Implies(And(t>=0,t<=15,p>=0,p<=1,sleep(t,p)==True),sleep(t+T,p)==True))))
s.add(Implies(constraint9,
              ForAll((p,t), Implies(And(t>=0,t<=15,p>=0,p<=1,sleep(t,p)==False),sleep(t+T,p)==False))))

#If process p is transmitting/not transmitting now(t) then it is transmitting/not transmitting after T(t+T)
s.add(Implies(constraint10,
              ForAll((p,t), Implies(And(t>=0,t<=15,p>=0,p<=1,transmit(t,p)>= 0),transmit(t+T,p)>= 0))))
s.add(Implies(constraint11,
              ForAll((p,t), Implies(And(t>=0,t<=15,p>=0,p<=1,transmit(t,p)==-1),transmit(t+T,p)==-1))))

#Only process 0 knows all packets at time 0
s.add(Implies(constraint12,
              ForAll((pack),Implies(And(pack>=0,pack<=2),knows(0,0,pack)==True))))

#At time 0 all processes (>=0) know 0 that represents garbage
s.add(Implies(constraint13,
              ForAll(p,
                     Implies(And(p>=0,p<=1),
                             knows(0,p,0)==True)))
      )

# at t=0, unaware of all packets
s.add(Implies(constraint14a,
              ForAll((p,pack),Implies(And(p>0,p<=1,pack>0,pack<=2),knows(0,p,pack)==False))))

#i transmit a packet I know= this is for processes > 0 # is it required?
#I know the packet that I am transmitting
s.add(Implies(constraint15,
              ForAll((t,p),Implies(And(t>=0,p>0,p<=1,t<=15,pack>=0,pack<=2,transmit(t,p)==pack),knows(t,p,pack)==True))))

#Once I know a packet then I know it forever
#s.add(Implies(constraint16, ForAll((t,c,p,packet), Implies(knows(t,p,packet)==True,knows(t+c,p,packet)==True))))
s.add(Implies(constraint16,
              ForAll((p,pack), Implies(And(t>=0,p>0,p<=1,t<=15,pack>=0,pack<=2,knows(t,p,pack)==True),knows(t+1,p,pack)==True))))


#one to one transmisssion and reception
s.add(Implies(constraint17,
              ForAll((t,p,pack),
                     Implies(And(knows(t+1,p,pack)==True,knows(t,p,pack)==False,pack>0,p>0,t>=0,p<=1,t<=15,pack<=2),#if process p knows a packet now and did not know it in the previous step
                             And(listen(t,p)==True,                                                                 #then p listened in the previous step,
                                 Exists(q,And(Or(q>p,q<p),q>=0,q<=1,transmit(t,q)==pack)),           #another process q transmitted that packet in the previous step
                                 ForAll(q1,Implies(And(not(q1==p),not(q1==q),q1>=0,q1<=1),transmit(t,q1)==-1))       #and no other process q1 except q was transmitting in the previous step
                                 )
                             )
                     )
              )
      )

#process p transmits a packet at time t+1 only if all processes know all previous packets at time t
s.add(Implies(constraint18,
              ForAll((p,pack),
                     Implies(And(transmit(t+1,p)==pack,t>=0,t<=15,p>=0,p<=1,pack>0,pack<=2),
                             ForAll((pack1,q), Implies(And((pack1 < pack), q>=0,q<=1, pack1>=0,pack1<=2),knows(t,q,pack1)==True))
                             )
                     )
              )
      )

#all processes eventually learn about all packets
s.add(Implies(constraint19,
              ForAll((pack,p),Implies(And(pack>0,pack<=2,p>=0,p<=1),knows(17,p,pack)==True))
              )
      )


#The method check() solves the asserted constraints
satResult = s.check(constraint1a,
                    constraint1,
                    constraint2,
                    constraint4,
                    constraint5,
                    constraint6,constraint7,
                    constraint8,constraint9,
                    constraint10,constraint11,
                    constraint12,
                    constraint13,
                    constraint14a,
                    constraint15,
                    constraint16,
                    constraint17,
                    constraint18,
                    constraint19
                    )
print satResult

if (satResult == z3.unsat):
    #print s.statistics
    print s.unsat_core()
else:
    print s.model()

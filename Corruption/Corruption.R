# ---------------------------------------------------------------------------------------------------- 
# This code implements moral hazard programs with lotteries
# based on the MATLAB code provided by
# Karaivanov, A. K. (2001): Computing Moral Hazard Programs with Lotteries Using Lotteries, 
# Working paper, Department of Economics, University of Chicago.

# Version: 31/10/2017
# Compatibility: R version 3.4.1 (2017-06-30)
# Author: Danilo Hiroshi Matsuoka   (danilomatsuoka@gmail.com)
# ---------------------------------------------------------------------------------------------------

#### Load Packages ####
library(lpSolveAPI)
library(VGAM)

################################### Program for Model A ###############################################

program.A=function(tau=0,a=.5,U=1,nw=50,nh=60,hmin=10^-8,hmax=1-10^-8,wmin=1,wmax=2,bl=1,bh=3){
  #tau    := Bureaucrat's relative risk aversion
  #a      := Output's conditional distribution parameter
  #U      := Reservation utility
  #nw     := Number of possible compensations
  #nh     := Number of possible actions
  #hmin   := Minimum action level
  #wmin   := Minimum compensation
  #bl     := Minimum bureaucratic efficiency
  #hmax   := Maximum action level
  #wmax   := Maximum compensation
  #bh     := Maximum bureaucratic efficiency
  #### Preliminaries ####
  
  nb=2                                                #The number of possible outcomes is fixed to 2
  wages=seq(wmin,wmax,length=nw)                      #Set of compensations (W)
  action=seq(hmin,hmax,length=nh)                     #Set of actions (H)
  output=c(bl,bh)                                     #Set of outputs (B)
  
  Prob=matrix(as.numeric(rbind(1-action^a,action^a))) #Conditional probabilities matrix
  Upper=rep(1,nh*nb*nw)                               #Vector of upper bounds for the choice variables
  Lower=rep(0,nh*nb*nw)                               #Vector of lower bounds for the choice variables
  
  #### Objective Function ####
  
  objective = -kronecker(rep(1, nh), kronecker(output, rep(1, nw))) + 
              kronecker(rep(1, nb*nh), wages)         #Principal's expected utility
  
  #### Matrix of Coefficients ####
  
  #Adding-up (to one) constraint
  Aeq1=rep(1, nh*nb*nw)                               #Coefficients                     
  beq1=1                                              #Intercept
  
  #Mother nature constraints
  Aeq2 = t(kronecker(diag(nh*nb), rep(1,nw))) - t(kronecker(t(kronecker(diag(nh),rep(1,nb))*
         (Prob%*%rep(1,nh))), rep(1,nb*nw)))          
  beq2 = rep(0,nh*nb)                                                   
  
  #Participation constraint
  A1 = -(1-tau)^-1*kronecker(rep(1, nb*nh),wages)^(1-tau) - 
   (kronecker(1-action, rep(1,nw*nb)))                
  b1 = -U                                             
  
  #Incentive compatibility constraints
  A2=matrix(NA,ncol=length(Aeq1),(nh-1)*(nh))
  for(iz in 1:nh){                                     #loop on the recommended action level
    if(iz==1) zh=(iz+1):nh
    if(iz==nh) zh=1:(iz-1)
    if(iz!=1&iz!=nh) zh = c(1:(iz-1),(iz+1):nh) 
    
    for(jz in 1:(nh-1)){                               #loop on the alternative action level
      A2[(nh-1)*(iz-1)+jz,] = kronecker(c(rep(0, iz-1), 1, rep(0, nh-iz)), 
                                        kronecker(rep(1,nb), A1[(nw*nb*(iz-1)+1):(nw*nb*(iz-1)+nw)]))+ 
        kronecker(c(rep(0, iz-1), 1, rep(0,nh-iz)), 
                  rep(1, nb*nw))*(kronecker(rep(1, nh),kronecker(
                    c(Prob[2*zh[jz]-1]/Prob[2*iz-1], Prob[2*zh[jz]]/Prob[2*iz]), 
                    -A1[(nw*nb*(zh[jz]-1)+1):(nw*nb*(zh[jz]-1)+nw)])))
    }}
  b2=rep(0,nh*(nh-1))
  
  Aeq=rbind(Aeq1, Aeq2)                          #Matrix of coefficients on the equality constraints
  beq=c(beq1,beq2)                               #and its vector of intercepts
  
  A=rbind(A1,A2)                                 #Matrix of coefficients on the inequality constraints
  b=c(b1, b2)                                    #and its vector of intercepts
  
  ######### Solving ########
  
  l=nw;m=nh;n=nb
  n.var=l*m*n                                    #Number of choice variables
  
  n.rest=                                        #Number of constraints
    m*n+                                         #Mother nature
    1+                                           #Sum up to 1
    m*(m-1)+                                     #Incentive compatibility
    1                                            #Participation constraints
  
  my.lp <- make.lp(n.rest, n.var)                #Create the linear program model object
  AA=rbind(A,Aeq)                                #Matrix of coefficients
  bb=c(b,beq)                                    #Vector of intercepts
  for(i in 1:n.var){                             #Seting the program's coefficients in my.lp object
    set.column(my.lp,i,AA[,i])
  }
  set.objfn(my.lp,objective)                     #Seting the objective function 
  set.constr.type(my.lp,                         #Seting the types of contraints
                 c(rep("<=",m*(m-1)+1),rep("=",m*n+1)))
  set.rhs(my.lp, bb)                             #Seting the intercepts
  set.bounds(my.lp, lower =Lower)                #Seting bounds on the choice variables
  set.bounds(my.lp, upper = Upper)
  
  solve(my.lp)
  
  resultado=get.variables(my.lp)                 #Values of the choice variables (solution)
  valor=get.objective(my.lp)                     #Value of the objective function (solution)
  
  #### Optimal Contract ####
  ww = kronecker(rep(1, nb*nh), wages)
  oo = kronecker(rep(1, nh), kronecker(output, rep(1, nw)))
  aa = kronecker(action,rep(1, nw*nb))
 
  xp=which(resultado>10^-4)
  #Recover the triples (h,b,w) associated to the nonzero optimal values
  final=round(cbind(aa[xp], oo[xp], ww[xp], resultado[xp]),digits=3) 
  colnames(final)=c("h","b","w","probabilidade")
  
  c(list(final),list(-valor))
}


################################### Program for Model B ###############################################

program.B=function(be=0,tau=0,U=.5,nw=60,wmin=1,nh=90,nb=5,hmin=10^-8){
  #be     := Degree of bureaucrat's altruism
  #tau    := Bureaucrat's relative risk aversion
  #U      := Reservation utility
  #nw     := Number of possible compensations
  #nh     := Number of possible actions
  #nb     := Number of possible outputs
  #hmin   := Minimum action level
  #wmin   := Minimum compensation
  #### Preliminaries ####
  
  wmax=nb                                               #Maximum compensation
  hmax=nb-10^-8                                         #Maximum action level 
  wages=seq(wmin,wmax,length=nw)                        #Set of compensations (W)
  action=seq(hmin,hmax,length=nh)                       #Set of action levels (H)
  output=seq(0,nb-1,by=1)                               #Set of outputs (B)
  
  Prob=matrix(unlist(lapply(1:nh,function(i) {          #Conditional probabilities matrix (beta-binomial)
       dbetabinom.ab(output, size=tail(output,n=1), 
                     shape1=action[i], shape2=(nb-action[i])*(1-action[i]/nb))} )),ncol=1)
  Upper=rep(1,nh*nb*nw)                                 #Vector of upper bounds for the choice variables
  Lower=rep(0,nh*nb*nw)                                 #Vector of lower bounds for the choice variables
  
  #### Objective Function ####
  
  objective = -kronecker(rep(1, nh), kronecker(output, rep(1, nw))) + kronecker(rep(1, nb*nh), wages)
  
  #### Matrix of Coefficients ####
  
  #Adding-up (to one) constraint
  Aeq1=rep(1, nh*nb*nw)
  beq1=1 
  
  #Mother nature constraints
  Aeq2 = t(kronecker(diag(nh*nb), rep(1,nw))) - 
         t(kronecker(t(kronecker(diag(nh),rep(1,nb))*(Prob%*%rep(1,nh))), rep(1,nb*nw)))
  beq2 = rep(0,nh*nb)
  
  #Participation constraint
  A1 = -(1-be)*((1-tau)^-1*kronecker(rep(1, nb*nh),wages)^(1-tau)) -
       be*kronecker(rep(1, nh), kronecker(output, rep(1, nw))) -(kronecker(1-action, rep(1,nw*nb)))
  b1 = -U
  
  #Incentive compatibility constraints
  A2=matrix(NA,ncol=length(Aeq1),(nh-1)*(nh))
  for(iz in 1:nh){                                      #Loop on the recommended action level
    if(iz==1) zh=(iz+1):nh
    if(iz==nh) zh=1:(iz-1)
    if(iz!=1&iz!=nh) zh = c(1:(iz-1),(iz+1):nh) 
    
    for(jz in 1:(nh-1)){                                #Loop on the alternative action level
      A2[(nh-1)*(iz-1)+jz,] = kronecker(c(rep(0, iz-1), 1, rep(0, nh-iz)), 
                                        kronecker(rep(1,nb), A1[(nw*nb*(iz-1)+1):(nw*nb*(iz-1)+nw)]))+ 
        kronecker(c(rep(0, iz-1), 1, rep(0,nh-iz)), 
                  rep(1, nb*nw))*(kronecker(rep(1, nh),kronecker(
                    sapply(1:nb,function(j) Prob[nb*zh[jz]-(nb-j)]/Prob[nb*iz-(nb-j)]),
                    -A1[(nw*nb*(zh[jz]-1)+1):(nw*nb*(zh[jz]-1)+nw)])))
    }}
  b2=rep(0,nh*(nh-1))
  
  Aeq=rbind(Aeq1, Aeq2)                                #Matrix of coefficients on the equality constraints
  beq=c(beq1,beq2)                                     #and its vector of intercepts
  
  A=rbind(A1,A2)                                       #Matrix of coefficients on the inequality constraints
  b=c(b1, b2)                                          #and its vector of intercepts
  
  ######### Solving ########
  
  l=length(wages)
  m=length(action)
  n=length(output)
  n.var=l*m*n                                          #Number of choice variables
  n.rest=                                              #Number of constraints
    m*n+                                               #Mother nature
    1+                                                 #Sum up to 1
    m*(m-1)+                                           #Incentive compatibility
    1  
  
  my.lp <- make.lp(n.rest, n.var)                      #Create the linear program model object
  AA=rbind(A,Aeq); bb=c(b,beq)
  for(i in 1:n.var){                                   #Seting the program's coefficients in my.lp object
    set.column(my.lp,i,AA[,i])
  }
  set.objfn(my.lp,objective)                           #Seting the objective function
  set.constr.type(my.lp, c(rep("<=",m*(m-1)+1),rep("=",m*n+1)))
  set.rhs(my.lp, bb)                                   #Seting the intercepts
  set.bounds(my.lp, lower =Lower)                      #Seting bounds on the choice variables
  set.bounds(my.lp, upper = Upper)
  
  solve(my.lp)
  
  resultado=get.variables(my.lp)                       #Values of the choice variables (solution)
  valor=round(get.objective(my.lp),digits=3)           #Value of the objective function (solution)
  
  #### Optimal Contract ####
  
  ww = kronecker(rep(1, nb*nh), wages)
  oo = kronecker(rep(1, nh), kronecker(output, rep(1, nw)))
  aa = kronecker(action,rep(1, nw*nb))
  
  xp=which(resultado>10^-4)
  #Recover the triples (h,b,w) associated to the nonzero optimal values
  final=round(cbind(aa[xp], oo[xp], ww[xp], resultado[xp]),digits=3)
  colnames(final)=c("h","b","w","probabilidade")
  
  c(list(final),list(-valor))}


program.A()     #Benchmark A 
program.B()     #Benchmark B

#Examples for varying parameters
program.A(a=.2)
program.A(tau=-.2)
program.B(be=.2)


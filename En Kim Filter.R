###---------------------------------------------------------------------------------------------------------------------------------------------###

# For technical introduction see:

#    - Kim, C.-J. (1994), “Dynamic linear models with Markov-switching,” Journal of Econometrics, 60(1-2), 1–22.
#    - Kim, C.-J., J. Piger, and R. Startz (2008), “Estimation of Markov regimeswitching regression models with endogenous switching,” Journal of Econometrics, 143(2), 263–273.
#    - Chang, Y., Y. Choi, and J. Y. Park (2017), “A new approach to model regime switching,” Journal of Econometrics, 196(1), 127–143.


# Script partly derived from following programs:

# R code replication of Morley, Nelson & Zivot (2003) by Matthew Zahn (https://matthew-zahn.github.io/files/code/MNZ_2003/uc_ur_programs.R)
#    - Structure of filtering approach.
#    - Parts of Kalman recursions within Kim filter and also partly recursions for likelihood and filter in L-UC model (not including smoother, 
#      forecasting, diagnostics and seasonality. Also initialization is changed).

# Published Gauss code of Sinclair (2009) (http://home.gwu.edu/%7Etsinc/asym.zip)
#    - Structure of Kim filtering approach.
#    - Parts of Hamilton recursions and approximations of Kim filter.
#    - As with the linear model, smoothing recurions, forecastin function, diagnostics are propietary. Technique of constraining the
#      Var-Cov matrix of system innovations Sigma also unfit in this case (see eq. 11).

# Source code of rnorm_multi() function from "faux" package
#    - Adopted technique to constrain Sigma matrix, which represents excerpt from the whole source code. Whole code of rnorm_multi() function is 
#      available under https://rdrr.io/github/debruine/faux/src/R/rnorm_multi.R.

# Source code of SE_to_Hessian() function from "HelpersMG" package
#    - Copied whole function since package is not available for current version of R. Original code can be downloaded under 
#      https://rdrr.io/cran/HelpersMG/src/R/SEfromHessian.R.

###---------------------------------------------------------------------------------------------------------------------------------------------###

# Load in data as Tx1 matrix
#data <- 

T <- nrow(data)

###---------------------------------------------------------------------------------------------------------------------------------------------###
###---------------------------------------------------------------------------------------------------------------------------------------------###
### Parameter constraints #########################################################################################################################
###---------------------------------------------------------------------------------------------------------------------------------------------###
###---------------------------------------------------------------------------------------------------------------------------------------------###


Par_constrain_En_Nl_UC <- function(par){
  
  const_par = par
  
  # Assures positive definite Var-Cov matrix Sigma of all system innovations
  # Also constrains Sigma so that correlation between xi and eta is not regime dependent
  sd_vec = c(exp(par[1]), exp(par[6]), exp(par[2]), 1)
  
  cor_matrix = matrix(0, 4, 4)
  diag(cor_matrix) = 1
  
  cor_matrix[4,1] = cor_matrix[4,2] = cor_matrix[1,4] = cor_matrix[2,4] = par[7] / (1 + abs(par[7])) 
  # Assures -1 > x > 1
  Sigma = (sd_vec %*% t(sd_vec)) * cor_matrix 
  
  # Standard deviations                                             
  const_par[1] = sqrt(Sigma[1,1])
  const_par[2] = sqrt(Sigma[3,3])
  const_par[6] = sqrt(Sigma[2,2])
  
  # Correlation
  const_par[7] = Sigma[4,1] / sqrt(Sigma[1,1])
  
  # Defines regimes
  const_par[5] = -exp(par[5])

  return(const_par)
  # (sd_xi_0, sd_omega, beta_0, beta_1, nu_1, sd_xi_1, varrho)
}


###---------------------------------------------------------------------------------------------------------------------------------------------###
###---------------------------------------------------------------------------------------------------------------------------------------------###
### Likelihood function ###########################################################################################################################
###---------------------------------------------------------------------------------------------------------------------------------------------###
###---------------------------------------------------------------------------------------------------------------------------------------------###


Kim_likelihood_En_Nl_UC <- function(par){
  
  #---------------------------------------------------------------------------------------#
  # Initialize filter 
  #---------------------------------------------------------------------------------------#
  
  # Reverse parameter transformation
  par = Par_constrain_En_Nl_UC(par)
  
  # For brevity the Sd of system innovations is named as the irregular component itself --> xi_0 denotes Sd of xi in regime 0
  xi_0   = par[1]        # Sd of RW process for regime 0
  omega  = par[2]        # Sd of measurement equation error
  beta_0 = par[3]        # Probit constant
  beta_1 = par[4]        # Probit covariate S_t-1
  nu_1   = par[5]        # Additional drift in regime 1
  varrho = par[7]        # Correlation between trend and regime innovations
  rho_0  = varrho * xi_0 # Transforms correlation to covariance in regime 0
  xi_1   = par[6]        # Sd of RW process in transition equation for regime 1
  rho_1  = varrho * xi_1 # Transforms correlation to covariance in regime 1
  
  # Transition matrix
  Tt = matrix(c(1, rep(0, 7), 1, 1, rep(0,8), 
                -1, 1, rep(0, 6),               
                -1, 0, 1, rep(0, 5),            
                -1, 0, 0, 1, rep(0, 4),         
                -1, rep(0, 3), 1, 0, 0, 0,     
                -1, rep(0, 4), 1, 0, 0,         
                -1, rep(0, 5)), 8, 8)          

  
  # Measurement matrix
  Z = matrix(c(1, 0, 1, rep(0, 5)), 1, 8)            
  
  # Transfer probit coefficients into probabilites
  p = 1 - pnorm(-beta_0 - beta_1) 
  q = pnorm(-beta_0)              
  
  # Initial unconditional regime probabilities (steady state unconditional probabilites)
  Pr_ct_0 = (1 - p) / (2 - p - q)
  Pr_ct_1 = (1 - q) / (2 - p - q)
  
  # Adjustment for changed moments of trend innovations
  m_00 = -dnorm(-beta_0) / pnorm(-beta_0)
  m_10 = -dnorm(-beta_0 - beta_1) / pnorm(-beta_0 - beta_1)
  m_01 =  dnorm(-beta_0) / (1 - pnorm(-beta_0))
  m_11 =  dnorm(-beta_0 - beta_1) / (1 - pnorm(-beta_0 - beta_1))
  
  ew_00 = matrix(c(rho_0, rep(0, 7)), 8) * m_00
  ew_10 = matrix(c(rho_0, rep(0, 7)), 8) * m_10
  ew_01 = matrix(c(rho_1, rep(0, 7)), 8) * m_01
  ew_11 = matrix(c(rho_1, rep(0, 7)), 8) * m_11
  
  Q_Cov_00 = matrix(c(-rho_0^2 * m_00 * (m_00 + beta_0), rep(0, 8)), 3)
  Q_Cov_10 = matrix(c(-rho_0^2 * m_10 * (m_10 + beta_0 + beta_1), rep(0, 8)), 3)
  Q_Cov_01 = matrix(c(-rho_1^2 * m_01 * (m_01 + beta_0), rep(0, 8)), 3)
  Q_Cov_11 = matrix(c(-rho_1^2 * m_11 * (m_11 + beta_0 + beta_1), rep(0, 8)), 3)
  
  # Var-Cov Matrix of innovations in transition equation
  Q_0 = matrix(0, 3, 3)
  Q_0[1,1] = xi_0^2
  Q_0[3,3] = omega^2
  
  Q_1 = matrix(0, 3, 3)
  Q_1[1,1] = xi_1^2
  Q_1[3,3] = omega^2
  
  # Matrix to expand Q so that it matches Var matrix of state vector
  R = matrix(c(1, rep(0, 17), 1, rep(0, 5)), 8, 3)
  
  # Vector for additional Drift in Regime 1
  lambda = matrix(c(nu_1, rep(0,7)), 8)
  
  # Initial values for state vector
  a_t_clt_00 = a_t_clt_10 = matrix(c(alpha_ini, rep(0,7)), 8)
  a_t_clt_01 = a_t_clt_11 = matrix(c(alpha_ini, rep(0,7)), 8) + lambda
  
  # Initial variance matrix for state vector (Exact diffuse initialization)
  P_t_clt_00 = P_t_clt_10 = P_t_clt_01 = P_t_clt_11 = diag(8) * 10000
  
  # Initializes log-likelihood to record values
  log_lik_T = 0
  
  
  #---------------------------------------------------------------------------------------#
  # Kim filter to set up likelihood function
  #---------------------------------------------------------------------------------------#
  
  for(i in 6:T) {
    
    #---------------------#    
    ### Kalman part 1/2 ###
    #---------------------#
    
    
    # One step ahead prediction error with state vector prediction from 
    # (t|t-1)
    v_t_00 = data[i] - Z %*% a_t_clt_00
    v_t_10 = data[i] - Z %*% a_t_clt_10
    v_t_01 = data[i] - Z %*% a_t_clt_01
    v_t_11 = data[i] - Z %*% a_t_clt_11
    
    # Variance of prediction error
    F_t_00 = Z %*% P_t_clt_00 %*% t(Z)
    F_t_10 = Z %*% P_t_clt_10 %*% t(Z)
    F_t_01 = Z %*% P_t_clt_01 %*% t(Z)
    F_t_11 = Z %*% P_t_clt_11 %*% t(Z)
    
    # Updating step 
    # (t|t, S_t, S_t-1)
    a_t_ct_00 = a_t_clt_00 + P_t_clt_00 %*% t(Z) %*% solve(F_t_00) %*% v_t_00
    a_t_ct_10 = a_t_clt_10 + P_t_clt_10 %*% t(Z) %*% solve(F_t_10) %*% v_t_10
    a_t_ct_01 = a_t_clt_01 + P_t_clt_01 %*% t(Z) %*% solve(F_t_01) %*% v_t_01
    a_t_ct_11 = a_t_clt_11 + P_t_clt_11 %*% t(Z) %*% solve(F_t_11) %*% v_t_11
    
    P_t_ct_00 = P_t_clt_00 - P_t_clt_00 %*% t(Z) %*% solve(F_t_00) %*% Z %*% P_t_clt_00
    P_t_ct_10 = P_t_clt_10 - P_t_clt_10 %*% t(Z) %*% solve(F_t_10) %*% Z %*% P_t_clt_10
    P_t_ct_01 = P_t_clt_01 - P_t_clt_01 %*% t(Z) %*% solve(F_t_01) %*% Z %*% P_t_clt_01
    P_t_ct_11 = P_t_clt_11 - P_t_clt_11 %*% t(Z) %*% solve(F_t_11) %*% Z %*% P_t_clt_11
    
    
    #-------------------#    
    ### Hamilton part ###
    #-------------------#
    
    
    # Computes Pr(S_t = j, S_t-1 = i) conditional on information at time t-1 
    # (t|t-1)
    Pr_clt_00 = q %*% Pr_ct_0
    Pr_clt_10 = (1 - p) %*% Pr_ct_1
    Pr_clt_01 = (1 - q) %*% Pr_ct_0
    Pr_clt_11 = p %*% Pr_ct_1
    
    # Density of y_t conditional on states (given by prediction error and prediction error variance from Kalman part)
    y_dens_clt_00 = dnorm(v_t_00, mean = 0, sd = sqrt(F_t_00))
    y_dens_clt_10 = dnorm(v_t_10, mean = 0, sd = sqrt(F_t_10))
    y_dens_clt_01 = dnorm(v_t_01, mean = 0, sd = sqrt(F_t_01))
    y_dens_clt_11 = dnorm(v_t_11, mean = 0, sd = sqrt(F_t_11))
    
    # Sum up joint densities of y_t and regimes to integrate out regime dependencies (receive density of y_t conditional on all information at 
    # (t|t-1))
    y_dens_clt = Pr_clt_00 * y_dens_clt_00 + Pr_clt_10 * y_dens_clt_10 + Pr_clt_01 * y_dens_clt_01 + Pr_clt_11 * y_dens_clt_11
    
    # Store approximate -likelihood (to revert minimization)
    log_lik_t = -log(y_dens_clt)
    
    # Update Pr(S_t = j, S_t-1 = i) now conditional on information at time t 
    # (t|t)
    Pr_ct_00 = Pr_clt_00 * y_dens_clt_00 / y_dens_clt
    Pr_ct_10 = Pr_clt_10 * y_dens_clt_10 / y_dens_clt
    Pr_ct_01 = Pr_clt_01 * y_dens_clt_01 / y_dens_clt
    Pr_ct_11 = Pr_clt_11 * y_dens_clt_11 / y_dens_clt
    
    #Sum up updated probabilities over possible realizations at t-1 to get regime probability at t only conditional on information at time t
    Pr_ct_0 = Pr_ct_00 + Pr_ct_10
    Pr_ct_1 = Pr_ct_01 + Pr_ct_11
    
    # Sum up log-likelihood over all iterations
    log_lik_T = log_lik_T + log_lik_t
    
    
    #------------------------#   
    ### Approximation part ###
    #------------------------#
    
    
    # Approximate updated values to break exponential growth of required values
    # (t|t, S_t)
    a_t_ct_0 = (a_t_ct_00 %*% Pr_ct_00 + a_t_ct_10 %*% Pr_ct_10) %*% solve(Pr_ct_0)
    a_t_ct_1 = (a_t_ct_01 %*% Pr_ct_01 + a_t_ct_11 %*% Pr_ct_11) %*% solve(Pr_ct_1)
    
    Pr_ct_00 = as.numeric(Pr_ct_00)
    Pr_ct_10 = as.numeric(Pr_ct_10)
    Pr_ct_01 = as.numeric(Pr_ct_01)
    Pr_ct_11 = as.numeric(Pr_ct_11)
    Pr_ct_0  = as.numeric(Pr_ct_0)
    Pr_ct_1  = as.numeric(Pr_ct_1)
    
    P_t_ct_0 = ((Pr_ct_00 * (P_t_ct_00 + (a_t_ct_0 - a_t_ct_00) %*% t(a_t_ct_0 - a_t_ct_00))) + (Pr_ct_10 * (P_t_ct_10 + (a_t_ct_0 - a_t_ct_10) %*% t(a_t_ct_0 - a_t_ct_10)))) / Pr_ct_0
    P_t_ct_1 = ((Pr_ct_01 * (P_t_ct_01 + (a_t_ct_1 - a_t_ct_01) %*% t(a_t_ct_1 - a_t_ct_01))) + (Pr_ct_11 * (P_t_ct_11 + (a_t_ct_1 - a_t_ct_11) %*% t(a_t_ct_1 - a_t_ct_11)))) / Pr_ct_1
    
    
    #---------------------#    
    ### Kalman part 2/2 ###
    #---------------------#  
    
    
    # Prediction step with approximated updates to complete loop 
    # (t+1|t)
    a_t_clt_00 = Tt %*% a_t_ct_0 + ew_00
    a_t_clt_10 = Tt %*% a_t_ct_1 + ew_10
    a_t_clt_01 = Tt %*% a_t_ct_0 + lambda + ew_01
    a_t_clt_11 = Tt %*% a_t_ct_1 + lambda + ew_11
    
    P_t_clt_00 = Tt %*% P_t_ct_0 %*% t(Tt) + R %*% (Q_0 + Q_Cov_00) %*% t(R) 
    P_t_clt_10 = Tt %*% P_t_ct_1 %*% t(Tt) + R %*% (Q_0 + Q_Cov_10) %*% t(R) 
    P_t_clt_01 = Tt %*% P_t_ct_0 %*% t(Tt) + R %*% (Q_1 + Q_Cov_01) %*% t(R)
    P_t_clt_11 = Tt %*% P_t_ct_1 %*% t(Tt) + R %*% (Q_1 + Q_Cov_11) %*% t(R)
    
  }
  
  #Final log-likelihood value
  return(log_lik_T)
  
} 


###---------------------------------------------------------------------------------------------------------------------------------------------###
###---------------------------------------------------------------------------------------------------------------------------------------------###
### Kim filter (like likelihood but returns filter output) ########################################################################################
###---------------------------------------------------------------------------------------------------------------------------------------------###
###---------------------------------------------------------------------------------------------------------------------------------------------###


Kim_filter_En_Nl_UC <- function(par, data){
  
  
  #---------------------------------------------------------------------------------------#
  # Initialize filter
  #---------------------------------------------------------------------------------------#
  
  xi_0   = par[1]        
  omega  = par[2]        
  beta_0 = par[3]        
  beta_1 = par[4]        
  nu_1   = par[5]        
  varrho = par[7]        
  rho_0  = varrho * xi_0 
  xi_1   = par[6]        
  rho_1  = varrho * xi_1 
  
  # Transition matrix
  Tt = matrix(c(1, rep(0, 7), 1, 1, rep(0,8),   
                -1, 1, rep(0, 6),               
                -1, 0, 1, rep(0, 5),            
                -1, 0, 0, 1, rep(0, 4),         
                -1, rep(0, 3), 1, 0, 0, 0,      
                -1, rep(0, 4), 1, 0, 0,         
                -1, rep(0, 5)), 8, 8)           

  # Measurement matrix
  Z = matrix(c(1, 0, 1, rep(0, 5)), 1, 8)              
  
  # Transfer probit coefficients into probabilites
  p = 1 - pnorm(-(beta_0 + beta_1)) 
  q = pnorm(-beta_0)                
  
  # Initial unconditional regime probabilities (steady state unconditional probabilites)
  Pr_ct_0 = (1-p) / (2 - p - q)
  Pr_ct_1 = (1-q) / (2 - p - q)
  
  #Sets up correlation between trend and regime-swichting innovations
  
  # Expectation of regime innovatins conditional on specific realizations
  m_00 = -dnorm(-beta_0) / pnorm(-beta_0)
  m_10 = -dnorm(-beta_0 - beta_1) / pnorm(-beta_0 - beta_1)
  m_01 =  dnorm(-beta_0) / (1 - pnorm(-beta_0))
  m_11 =  dnorm(-beta_0 - beta_1) / (1 - pnorm(-beta_0 - beta_1))
  
  # Scales m_ij
  ew_00 = matrix(c(rho_0, rep(0, 7)), 8) * m_00
  ew_10 = matrix(c(rho_0, rep(0, 7)), 8) * m_10
  ew_01 = matrix(c(rho_1, rep(0, 7)), 8) * m_01
  ew_11 = matrix(c(rho_1, rep(0, 7)), 8) * m_11
  
  # Matrix to adjust Var of innovations according to correlation
  Q_Cov_00 = matrix(c(-rho_0^2 * m_00 * (m_00 + beta_0), rep(0, 8)), 3)
  Q_Cov_10 = matrix(c(-rho_0^2 * m_10 * (m_10 + beta_0 + beta_1), rep(0, 8)), 3)
  Q_Cov_01 = matrix(c(-rho_1^2 * m_01 * (m_01 + beta_0), rep(0, 8)), 3)
  Q_Cov_11 = matrix(c(-rho_1^2 * m_11 * (m_11 + beta_0 + beta_1), rep(0, 8)), 3)
  
  # Var-Cov Matrix of innovations in transition equation
  Q_0 = matrix(0, 3, 3)
  Q_0[1,1] = xi_0^2
  Q_0[3,3] = omega^2
  
  Q_1 = matrix(0, 3, 3)
  Q_1[1,1] = xi_1^2
  Q_1[3,3] = omega^2
  
  # Matrix to expand Q so that it matches Var matrix of state vector
  R = matrix(c(1, rep(0, 17), 1, rep(0, 5)), 8, 3)
  
  # Vector for additional Drift in Regime 1
  lambda = matrix(c(nu_1, rep(0,7)), 8)
  
  # Initial values for state vector
  a_t_clt_00 = a_t_clt_10 = matrix(c(alpha_ini, rep(0,7)), 8)
  a_t_clt_01 = a_t_clt_11 = matrix(c(alpha_ini, rep(0,7)), 8) + lambda
  
  # Initial variance matrix for state vector (Exact diffuse initialization)
  P_t_clt_00 = P_t_clt_10 =  P_t_clt_01 = P_t_clt_11 = diag(8) * 10000
  
  # Initializes output objects
  a_clt_array = array(0, c(8, 4, T))
  P_clt_array = array(0, c(8, 32, T))
  a_ct_array  = array(0, c(8, 2, T))
  P_ct_array  = array(0, c(8, 16, T))
  Prob_t_clt  = matrix(0, T, 2)
  Prob_t_ct   = matrix(0, T, 2)
  v_ct_mat    = matrix(0, T, 4)
  F_ct_mat    = matrix(0, T, 4)
  
  
  #---------------------------------------------------------------------------------------#
  # Kim filter to get filtered values 
  #---------------------------------------------------------------------------------------#
  
  
  for(i in 6:T){
    
    
    #---------------------#
    ### Kalman part 1/2 ###
    #---------------------#
    
    
    # One step ahead prediction error
    v_t_00 = data[i] - Z %*% a_t_clt_00
    v_t_10 = data[i] - Z %*% a_t_clt_10
    v_t_01 = data[i] - Z %*% a_t_clt_01
    v_t_11 = data[i] - Z %*% a_t_clt_11
    
    # Variance of prediction error
    F_t_00 = Z %*% P_t_clt_00 %*% t(Z)
    F_t_10 = Z %*% P_t_clt_10 %*% t(Z)
    F_t_01 = Z %*% P_t_clt_01 %*% t(Z)
    F_t_11 = Z %*% P_t_clt_11 %*% t(Z)
    
    # Updating step (t|t)
    a_t_ct_00 = a_t_clt_00 + P_t_clt_00 %*% t(Z) %*% solve(F_t_00) %*% v_t_00
    a_t_ct_10 = a_t_clt_10 + P_t_clt_10 %*% t(Z) %*% solve(F_t_10) %*% v_t_10
    a_t_ct_01 = a_t_clt_01 + P_t_clt_01 %*% t(Z) %*% solve(F_t_01) %*% v_t_01
    a_t_ct_11 = a_t_clt_11 + P_t_clt_11 %*% t(Z) %*% solve(F_t_11) %*% v_t_11
    
    P_t_ct_00 = P_t_clt_00 - P_t_clt_00 %*% t(Z) %*% solve(F_t_00) %*% Z %*% P_t_clt_00
    P_t_ct_10 = P_t_clt_10 - P_t_clt_10 %*% t(Z) %*% solve(F_t_10) %*% Z %*% P_t_clt_10
    P_t_ct_01 = P_t_clt_01 - P_t_clt_01 %*% t(Z) %*% solve(F_t_01) %*% Z %*% P_t_clt_01
    P_t_ct_11 = P_t_clt_11 - P_t_clt_11 %*% t(Z) %*% solve(F_t_11) %*% Z %*% P_t_clt_11
    
    # Store prediction errors and variances
    v_ct_mat[i, 1] = v_t_00
    v_ct_mat[i, 2] = v_t_10
    v_ct_mat[i, 3] = v_t_01
    v_ct_mat[i, 4] = v_t_11
    
    F_ct_mat[i, 1] = F_t_00
    F_ct_mat[i, 2] = F_t_10
    F_ct_mat[i, 3] = F_t_01
    F_ct_mat[i, 4] = F_t_11
    
    
    #-------------------#
    ### Hamilton part ###
    #-------------------#
    
    
    # Computes Pr(S_t = j, S_t-1 = i) conditional on information at time t-1
    Pr_clt_00 = q %*% Pr_ct_0
    Pr_clt_10 = (1 - p) %*% Pr_ct_1
    Pr_clt_01 = (1 - q) %*% Pr_ct_0
    Pr_clt_11 = p %*% Pr_ct_1
    
    # Pr of S_t = j conditional on t = t-1 is given by summarizing over all regimes at t = t-1
    Pr_clt_0 = Pr_clt_00 + Pr_clt_10
    Pr_clt_1 = Pr_clt_01 + Pr_clt_11
    
    
    # Density of y_t conditional on states (given by prediction error and prediction error variance from Kalman part)
    y_dens_clt_00 = dnorm(v_t_00, mean = 0, sd = sqrt(F_t_00))
    y_dens_clt_10 = dnorm(v_t_10, mean = 0, sd = sqrt(F_t_10))
    y_dens_clt_01 = dnorm(v_t_01, mean = 0, sd = sqrt(F_t_01))
    y_dens_clt_11 = dnorm(v_t_11, mean = 0, sd = sqrt(F_t_11))
    
    # Sum up joint densities of y_t and states to integrate out regime-condition (receive density of y_t conditional on all information at t = t-1)
    y_dens_clt = Pr_clt_00 * y_dens_clt_00 + Pr_clt_10 * y_dens_clt_10 + Pr_clt_01 * y_dens_clt_01 + Pr_clt_11 * y_dens_clt_11
    
    # Update Pr(S_t = j, S_t-1 = i) now conditional on information at time t
    Pr_ct_00 = Pr_clt_00 * y_dens_clt_00 / y_dens_clt
    Pr_ct_10 = Pr_clt_10 * y_dens_clt_10 / y_dens_clt
    Pr_ct_01 = Pr_clt_01 * y_dens_clt_01 / y_dens_clt
    Pr_ct_11 = Pr_clt_11 * y_dens_clt_11 / y_dens_clt
    
    #Sum up updated probabilities over possible realizations at t-1 to get regime probability at t only conditional on information at time t
    Pr_ct_0 = Pr_ct_00 + Pr_ct_10
    Pr_ct_1 = Pr_ct_01 + Pr_ct_11
    
    
    # Records predicted probabilites 
    Prob_t_clt[i, 1] = Pr_clt_0
    Prob_t_clt[i, 2] = Pr_clt_1 #Two values are actually necessarry even though both probs add up to one, since some extremly small probs could be rounded to 1 and/ or zero
    
    # Records updated probability
    # Hier erklären warum NACH erster Berechnung erst in U_Prob aufgenommen --> initialer Wert ist nicht a_1 wie bei State Vector sondern Pr(S_t-1 = i | I_t-1) und t-1 = 0
    Prob_t_ct[i, 1] = Pr_ct_0
    Prob_t_ct[i, 2] = Pr_ct_1
    
    
    #------------------------#
    ### Approximation part ###
    #------------------------#
    
    
    # Approximate updated values for state vector and Var matrix to break exponential growth of required values
    a_t_ct_0 = (a_t_ct_00 %*% Pr_ct_00 + a_t_ct_10 %*% Pr_ct_10) %*% solve(Pr_ct_0)
    a_t_ct_1 = (a_t_ct_01 %*% Pr_ct_01 + a_t_ct_11 %*% Pr_ct_11) %*% solve(Pr_ct_1)
    
    Pr_ct_00 = as.numeric(Pr_ct_00)
    Pr_ct_10 = as.numeric(Pr_ct_10)
    Pr_ct_01 = as.numeric(Pr_ct_01)
    Pr_ct_11 = as.numeric(Pr_ct_11)
    Pr_ct_0  = as.numeric(Pr_ct_0)
    Pr_ct_1  = as.numeric(Pr_ct_1)
    
    P_t_ct_0 = ((Pr_ct_00 * (P_t_ct_00 + (a_t_ct_0 - a_t_ct_00) %*% t(a_t_ct_0 - a_t_ct_00))) + (Pr_ct_10 * (P_t_ct_10 + (a_t_ct_0 - a_t_ct_10) %*% t(a_t_ct_0 - a_t_ct_10)))) / Pr_ct_0
    P_t_ct_1 = ((Pr_ct_01 * (P_t_ct_01 + (a_t_ct_1 - a_t_ct_01) %*% t(a_t_ct_1 - a_t_ct_01))) + (Pr_ct_11 * (P_t_ct_11 + (a_t_ct_1 - a_t_ct_11) %*% t(a_t_ct_1 - a_t_ct_11)))) / Pr_ct_1
    
    
    #---------------------#
    ### Kalman part 2/2 ###
    #---------------------#
    
    
    #Store predicted values 
    a_clt_array[, 1, i] = a_t_clt_00
    a_clt_array[, 2, i] = a_t_clt_10
    a_clt_array[, 3, i] = a_t_clt_01
    a_clt_array[, 4, i] = a_t_clt_11
    
    P_clt_array[, 1:8, i]   = P_t_clt_00
    P_clt_array[, 9:16, i]  = P_t_clt_10
    P_clt_array[, 17:24, i] = P_t_clt_01
    P_clt_array[, 25:32, i] = P_t_clt_11
    
    # Store updated values 
    a_ct_array[, 1, i] = a_t_ct_0
    a_ct_array[, 2, i] = a_t_ct_1
    
    P_ct_array[, 1:8, i]  = P_t_ct_0
    P_ct_array[, 9:16, i] = P_t_ct_1
    
    # Prediction step with approximated updates to complete loop 
    a_t_clt_00 = Tt %*% a_t_ct_0 + ew_00
    a_t_clt_10 = Tt %*% a_t_ct_1 + ew_10
    a_t_clt_01 = Tt %*% a_t_ct_0 + lambda + ew_01
    a_t_clt_11 = Tt %*% a_t_ct_1 + lambda + ew_11
    
    P_t_clt_00 = Tt %*% P_t_ct_0 %*% t(Tt) + R %*% (Q_0 + Q_Cov_00) %*% t(R) 
    P_t_clt_10 = Tt %*% P_t_ct_1 %*% t(Tt) + R %*% (Q_0 + Q_Cov_10) %*% t(R) 
    P_t_clt_01 = Tt %*% P_t_ct_0 %*% t(Tt) + R %*% (Q_1 + Q_Cov_01) %*% t(R)
    P_t_clt_11 = Tt %*% P_t_ct_1 %*% t(Tt) + R %*% (Q_1 + Q_Cov_11) %*% t(R)
    
  }
  
  # Output of filtered values
  return(list(a_clt    = a_clt_array,   
              P_clt    = P_clt_array,   
              a_ct     = a_ct_array,    
              P_ct     = P_ct_array,    
              Prob_clt = Prob_t_clt,    
              Prob_ct  = Prob_t_ct,     
              Pred_err = v_ct_mat,      
              Pred_err_Var = F_ct_mat))
  
}


###---------------------------------------------------------------------------------------------------------------------------------------------###
###---------------------------------------------------------------------------------------------------------------------------------------------###
### Kim smoother ##################################################################################################################################
###---------------------------------------------------------------------------------------------------------------------------------------------###
###---------------------------------------------------------------------------------------------------------------------------------------------###


Kim_Smoother_En_Nl_UC <- function(par, Filter_output, level){
  
  
  #---------------------------------------------------------------------------------------#
  # Initialize smoother
  #---------------------------------------------------------------------------------------#
  
  
  # Initialize smoother output
  a_cT_array = array(0, c(8, 3, T))
  P_cT_array = array(0, c(8, 16, T))
  Pr_cT_mat  = matrix(0, T, 2)
  CI_a_cT_array = array(0, c(8, 2, T))
  
  # Provide system matrix
  Tt = matrix(c(1, rep(0, 7), 1, 1, rep(0,8), 
                -1, 1, rep(0, 6), 
                -1, 0, 1, rep(0, 5), 
                -1, 0, 0, 1, rep(0, 4), 
                -1, rep(0, 3), 1, 0, 0, 0, 
                -1, rep(0, 4), 1, 0, 0, 
                -1, rep(0, 5)), 8, 8)                   
  
  
  # Provide transition probabilites
  beta_0 = par[3]
  beta_1 = par[4]
  
  p = 1 - pnorm(-(beta_0 + beta_1)) 
  q = pnorm(-beta_0)                
  
  # Realizations for t = T of Kim filter and Kim smoother are identical
  Pr_cT_0 = Filter_output[["Prob_ct"]][T, 1]
  Pr_cT_1 = Filter_output[["Prob_ct"]][T, 2]
  
  a_t1_cT_0 = a_cT_array[, 1, T] = Filter_output[["a_ct"]][, 1, T] %>% as.matrix(., 2)
  a_t1_cT_1 = a_cT_array[, 2, T] = Filter_output[["a_ct"]][, 2, T] %>% as.matrix(., 2)
  a_cT_array[, 3, T] = Pr_cT_0 * a_cT_array[1, 1, T] + Pr_cT_1 * a_cT_array[1, 2, T]
  
  P_t1_cT_0 = P_cT_array[, 1:8, T]  = Filter_output[["P_ct"]][, 1:8, T]
  P_t1_cT_1 = P_cT_array[, 9:16, T] = Filter_output[["P_ct"]][, 9:16, T]
  
  
  #---------------------------------------------------------------------------------------#
  # Kim smoother (backwards) iteration 
  #---------------------------------------------------------------------------------------#
  
  
  for(i in (T-1):5){
    
    # Load necessary filtered values for each iteration
    Pr_ct_0  = Filter_output[["Prob_ct"]][i, 1]
    Pr_ct_1  = Filter_output[["Prob_ct"]][i, 2]
    
    Pr_clt_0 = Filter_output[["Prob_clt"]][i + 1, 1] #Note: value read in as (t+1|t), equivalent to (t|t-1) with lead = 1
    Pr_clt_1 = Filter_output[["Prob_clt"]][i + 1, 2]
    
    a_t_ct_0 = Filter_output[["a_ct"]][, 1, i] %>% as.matrix(., 2)
    a_t_ct_1 = Filter_output[["a_ct"]][, 2, i] %>% as.matrix(., 2)
    
    a_t1_ct_00 = Filter_output[["a_clt"]][, 1, i + 1] %>% as.matrix(., 2) #Note: values read in as (t+1|t), equivalent to (t|t-1) with lead = 1
    a_t1_ct_10 = Filter_output[["a_clt"]][, 2, i + 1] %>% as.matrix(., 2)
    a_t1_ct_01 = Filter_output[["a_clt"]][, 3, i + 1] %>% as.matrix(., 2)
    a_t1_ct_11 = Filter_output[["a_clt"]][, 4, i + 1] %>% as.matrix(., 2)
    
    P_t_ct_0 = Filter_output[["P_ct"]][, 1:8, i]
    P_t_ct_1 = Filter_output[["P_ct"]][, 9:16, i]
    
    P_t1_ct_00 = Filter_output[["P_clt"]][, 1:8, i + 1] #Note: values read in as (t+1|t), equivalent to (t|t-1) with lead = 1
    P_t1_ct_10 = Filter_output[["P_clt"]][, 9:16, i + 1]
    P_t1_ct_01 = Filter_output[["P_clt"]][, 17:24, i + 1]
    P_t1_ct_11 = Filter_output[["P_clt"]][, 25:32, i + 1]
    
    
    #-------------------#
    ### Hamilton part ###
    #-------------------#
    
    
    # Compute Pr(S_t = j, S_t+1 = k) conditional on all information
    # Here Pr_cT_jk: _cT_01 implies Pr(S_t+1 = 1, S_t = 0 | T) // NOTE: Probabilites conditional on t retain prev. notation --> _ct_01: conditional on t Pr(S_t = 1, S_t-1 = 0 | t)
    # (t|T) 
    Pr_cT_00 = (Pr_cT_0 * Pr_ct_0 * q)       / Pr_clt_0
    Pr_cT_10 = (Pr_cT_0 * Pr_ct_1 * (1 - p)) / Pr_clt_0 
    Pr_cT_01 = (Pr_cT_1 * Pr_ct_0 * (1 - q)) / Pr_clt_1 
    Pr_cT_11 = (Pr_cT_1 * Pr_ct_1 * p)       / Pr_clt_1 
    
    # Compute Pr(S_t = j | all information) // NOTE: To derive at unconditional probability of Pr(S_t) on has to sum over all regimes at t = t + 1 (in difference to t = t - 1 in the filter) 
    # (t|T)
    Pr_cT_0 = Pr_cT_00 + Pr_cT_01
    Pr_cT_0 = ifelse(Pr_cT_0 == 0, 1e-10, Pr_cT_0) # Recursion not possibel when estimated probability for one regime equals 0 or is rounded to zero by R
    Pr_cT_1 = Pr_cT_10 + Pr_cT_11
    Pr_cT_1 = ifelse(Pr_cT_1 == 0, 1e-10, Pr_cT_1)
    
    # Record smoothed probabilites
    Pr_cT_mat[i, 1] = Pr_cT_0
    Pr_cT_mat[i, 2] = Pr_cT_1
    
    
    #---------------------#
    ### Kalman part 1/2 ###
    #---------------------#
    
    
    # Derive smoothed State Vector. NOTE: again _cT_01: S_t = 0 and S_t+1 = 1 // _ct_01: S_t-1 = 0 and S_t = 1
    # (t|T)
    Ph_00 = P_t_ct_0 %*% t(Tt) %*% solve(P_t1_ct_00) #Ph --> P help matrix
    Ph_10 = P_t_ct_1 %*% t(Tt) %*% solve(P_t1_ct_10)
    Ph_01 = P_t_ct_0 %*% t(Tt) %*% solve(P_t1_ct_01)
    Ph_11 = P_t_ct_1 %*% t(Tt) %*% solve(P_t1_ct_11)
    
    a_t_cT_00 = a_t_ct_0 + Ph_00 %*% (a_t1_cT_0 - a_t1_ct_00)
    a_t_cT_10 = a_t_ct_1 + Ph_10 %*% (a_t1_cT_0 - a_t1_ct_10)
    a_t_cT_01 = a_t_ct_0 + Ph_01 %*% (a_t1_cT_1 - a_t1_ct_01)
    a_t_cT_11 = a_t_ct_1 + Ph_11 %*% (a_t1_cT_1 - a_t1_ct_11)
    
    # Same for State Variance Matrix
    P_t_cT_00 = P_t_ct_0 + Ph_00 %*% (P_t1_cT_0 - P_t1_ct_00) %*% t(Ph_00)
    P_t_cT_10 = P_t_ct_1 + Ph_10 %*% (P_t1_cT_0 - P_t1_ct_10) %*% t(Ph_10)
    P_t_cT_01 = P_t_ct_0 + Ph_01 %*% (P_t1_cT_1 - P_t1_ct_01) %*% t(Ph_01)
    P_t_cT_11 = P_t_ct_1 + Ph_11 %*% (P_t1_cT_1 - P_t1_ct_11) %*% t(Ph_11)
    
    # Confidence intervalls for smoothed state vector
    u_a_t_cT_00 = a_t_cT_00 + qnorm(1 - (1 - level) / 2) * sqrt(P_t_cT_00[1,1])
    u_a_t_cT_10 = a_t_cT_10 + qnorm(1 - (1 - level) / 2) * sqrt(P_t_cT_10[1,1])
    u_a_t_cT_01 = a_t_cT_01 + qnorm(1 - (1 - level) / 2) * sqrt(P_t_cT_01[1,1])
    u_a_t_cT_11 = a_t_cT_11 + qnorm(1 - (1 - level) / 2) * sqrt(P_t_cT_11[1,1])
    
    l_a_t_cT_00 = a_t_cT_00 - qnorm(1 - (1 - level) / 2) * sqrt(P_t_cT_00[1,1])
    l_a_t_cT_10 = a_t_cT_10 - qnorm(1 - (1 - level) / 2) * sqrt(P_t_cT_10[1,1])
    l_a_t_cT_01 = a_t_cT_01 - qnorm(1 - (1 - level) / 2) * sqrt(P_t_cT_01[1,1])
    l_a_t_cT_11 = a_t_cT_11 - qnorm(1 - (1 - level) / 2) * sqrt(P_t_cT_11[1,1])
    
    
    #------------------------#
    ### Approximation part ###
    #------------------------#
    
    
    # Approximate smoothed values, so that only conditional on current regime
    # Note: In difference to the filter, probabilites are averaged over all possible regimes at t = t + 1 (not t = t - 1)
    # (t|T)
    a_t_cT_0 = ((Pr_cT_00 * a_t_cT_00) + (Pr_cT_01 * a_t_cT_01)) / Pr_cT_0
    a_t_cT_1 = ((Pr_cT_10 * a_t_cT_10) + (Pr_cT_11 * a_t_cT_11)) / Pr_cT_1
    
    # Also approximate confidence intervals
    u_a_t_cT_0 = ((Pr_cT_00 * u_a_t_cT_00) + (Pr_cT_01 * u_a_t_cT_01)) / Pr_cT_0
    u_a_t_cT_1 = ((Pr_cT_10 * u_a_t_cT_10) + (Pr_cT_11 * u_a_t_cT_11)) / Pr_cT_1
    
    l_a_t_cT_0 = ((Pr_cT_00 * l_a_t_cT_00) + (Pr_cT_01 * l_a_t_cT_01)) / Pr_cT_0
    l_a_t_cT_1 = ((Pr_cT_10 * l_a_t_cT_10) + (Pr_cT_11 * l_a_t_cT_11)) / Pr_cT_1
    
    # Same for State Variance Matrix
    P_t_cT_0 = (Pr_cT_00 * (P_t_cT_00 + (a_t_cT_0 - a_t_cT_00) %*% t(a_t_cT_0 - a_t_cT_00)) + Pr_cT_01 * (P_t_cT_01 + (a_t_cT_0 - a_t_cT_01) %*% t(a_t_cT_0 - a_t_cT_01))) / Pr_cT_0
    P_t_cT_1 = (Pr_cT_10 * (P_t_cT_10 + (a_t_cT_1 - a_t_cT_10) %*% t(a_t_cT_1 - a_t_cT_10)) + Pr_cT_11 * (P_t_cT_11 + (a_t_cT_1 - a_t_cT_11) %*% t(a_t_cT_1 - a_t_cT_11))) / Pr_cT_1
    
    # One can again average the State Vector across all possible realizations for unconditinal average
    a_t_cT = a_t_cT_0 * Pr_cT_0 + a_t_cT_1 * Pr_cT_1
    
    u_a_t_cT = Pr_cT_0 * u_a_t_cT_0 + Pr_cT_1 * u_a_t_cT_1
    l_a_t_cT = Pr_cT_0 * l_a_t_cT_0 + Pr_cT_1 * l_a_t_cT_1
    
    # Output smoothed vectors and Var matrices
    a_cT_array[, 1, i] = a_t_cT_0
    a_cT_array[, 2, i] = a_t_cT_1
    a_cT_array[, 3, i] = a_t_cT
    
    CI_a_cT_array[, 1, i] = u_a_t_cT
    CI_a_cT_array[, 2, i] = l_a_t_cT
    
    P_cT_array[, 1:8, i] = P_t_cT_0
    P_cT_array[, 9:16, i] = P_t_cT_1
    
    
    #---------------------#
    ### Kalman part 2/2 ###
    #---------------------#
    
    
    # Update smoothed values for State Vector and Var Matrix for next iteration
    # (t + 1|T) in next iteration
    a_t1_cT_0 = a_t_cT_0
    a_t1_cT_1 = a_t_cT_1
    
    P_t1_cT_0 = P_t_cT_0
    P_t1_cT_1 = P_t_cT_1
    
  }
  
  return(list(a_cT    = a_cT_array,     # Smoothed state vector
              P_cT    = P_cT_array,     # Smoothed state vector var
              Pr_cT   = Pr_cT_mat,      # Smoothed regime probs
              a_CI_cT = CI_a_cT_array)) # Confidence intervalls state vector
  
}



###---------------------------------------------------------------------------------------------------------------------------------------------###
###---------------------------------------------------------------------------------------------------------------------------------------------###
### Kim filter forecast ###########################################################################################################################
###---------------------------------------------------------------------------------------------------------------------------------------------###
###---------------------------------------------------------------------------------------------------------------------------------------------###


Kim_forecast_En_Nl_UC <- function(par, State_Vec, State_Var, Prob_0, Prob_1, level, n_ahead){
  
  
  #---------------------------------------------------------------------------------------#
  # Initialize forecast filter
  #---------------------------------------------------------------------------------------#
  
  # Load parameters
  xi_0   = par[1]        
  omega  = par[2]        
  beta_0 = par[3]        
  beta_1 = par[4]        
  nu_1   = par[5]        
  varrho = par[7]        
  rho_0  = varrho * xi_0 
  xi_1   = par[6]       
  rho_1  = varrho * xi_1 
  
  
  # Transition matrix
  Tt = matrix(c(1, rep(0, 7), 1, 1, rep(0,8),  
                -1, 1, rep(0, 6),               
                -1, 0, 1, rep(0, 5),           
                -1, 0, 0, 1, rep(0, 4),        
                -1, rep(0, 3), 1, 0, 0, 0,      
                -1, rep(0, 4), 1, 0, 0,         
                -1, rep(0, 5)), 8, 8)           

  # Measurement matrix
  Z = matrix(c(1, 0, 1, rep(0, 5)), 1, 8)                   
  
  # Transfer probit coefficients into probabilites
  p = 1 - pnorm(-(beta_0 + beta_1)) 
  q = pnorm(-beta_0)                
  
  # Initial unconditional regime probabilities (steady state unconditional probabilites)
  Pr_ct_0 = (1-p) / (2 - p - q)
  Pr_ct_1 = (1-q) / (2 - p - q)
  
  # Var-Cov Matrix of innovations in transition equation
  Q_0 = matrix(0, 3, 3)
  Q_0[1,1] = xi_0^2
  Q_0[3,3] = omega^2
  
  Q_1 = matrix(0, 3, 3)
  Q_1[1,1] = xi_1^2
  Q_1[3,3] = omega^2
  
  #Sets up correlation between trend and regime-swichting innovations
  m_00 = -dnorm(-beta_0) / pnorm(-beta_0)
  m_10 = -dnorm(-beta_0 - beta_1) / pnorm(-beta_0 - beta_1)
  m_01 =  dnorm(-beta_0) / (1 - pnorm(-beta_0))
  m_11 =  dnorm(-beta_0 - beta_1) / (1 - pnorm(-beta_0 - beta_1))
  
  ew_00 = matrix(c(rho_0, rep(0, 7)), 8) * m_00
  ew_10 = matrix(c(rho_0, rep(0, 7)), 8) * m_10
  ew_01 = matrix(c(rho_1, rep(0, 7)), 8) * m_01
  ew_11 = matrix(c(rho_1, rep(0, 7)), 8) * m_11
  
  Q_Cov_00 = matrix(c(-rho_0^2 * m_00 * (m_00 + beta_0), rep(0, 8)), 3)
  Q_Cov_10 = matrix(c(-rho_0^2 * m_10 * (m_10 + beta_0 + beta_1), rep(0, 8)), 3)
  Q_Cov_01 = matrix(c(-rho_1^2 * m_01 * (m_01 + beta_0), rep(0, 8)), 3)
  Q_Cov_11 = matrix(c(-rho_1^2 * m_11 * (m_11 + beta_0 + beta_1), rep(0, 8)), 3)
  
  # Matrix to expand Q so that it matches Var matrix of state vector
  R = matrix(c(1, rep(0, 17), 1, rep(0, 5)), 8, 3)
  
  # Vector for additional Drift in Regime 1
  lambda = matrix(c(nu_1, rep(0,7)), 8)
  
  # Initial values for State Vector
  a_t_clt_00 = State_Vec[, 1, T] %>% as.matrix(., 2)
  a_t_clt_10 = State_Vec[, 2, T] %>% as.matrix(., 2)
  a_t_clt_01 = State_Vec[, 3, T] %>% as.matrix(., 2)
  a_t_clt_11 = State_Vec[, 4, T] %>% as.matrix(., 2)
  
  # Initial variance matrix for State Vector
  P_t_clt_00 = State_Var[, 1:8, T]
  P_t_clt_10 = State_Var[, 9:16, T]
  P_t_clt_01 = State_Var[, 17:24, T]
  P_t_clt_11 = State_Var[, 25:32, T]
  
  # Initial unconditional regime probabilities (steady state unconditional probabilites)
  Pr_clt_0 = Prob_0[T]
  Pr_clt_1 = Prob_1[T]
  
  # Initializes output objects
  a_clt_array        = array(0, c(8, 4, n_ahead))
  P_clt_array        = array(0, c(8, 32, n_ahead))
  a_clt_approx_array = array(0, c(8, 9, n_ahead))
  P_clt_approx_array = array(0, c(8, 16, n_ahead))
  Prob_t_clt         = matrix(0, n_ahead, 2)
  y_clt_mat          = matrix(0, n_ahead, 1)
  
  
  #---------------------------------------------------------------------------------------#
  # Kim filter (forwards) recursion (without updating steps)
  #---------------------------------------------------------------------------------------#
  
  
  for(i in 1:n_ahead){
    
    
    #---------------------#
    ### Kalman part 1/2 ###
    #---------------------#
    
    
    # Variance of prediction error
    F_t_00 = Z %*% P_t_clt_00 %*% t(Z)  
    F_t_10 = Z %*% P_t_clt_10 %*% t(Z)  
    F_t_01 = Z %*% P_t_clt_01 %*% t(Z)  
    F_t_11 = Z %*% P_t_clt_11 %*% t(Z) 
    
    # Computes prediction intervals
    u_a_t_clt_00 = a_t_clt_00 + qnorm(1 - (1 - level) / 2) * sqrt(F_t_00[1,1])
    u_a_t_clt_10 = a_t_clt_10 + qnorm(1 - (1 - level) / 2) * sqrt(F_t_10[1,1])
    u_a_t_clt_01 = a_t_clt_01 + qnorm(1 - (1 - level) / 2) * sqrt(F_t_01[1,1])
    u_a_t_clt_11 = a_t_clt_11 + qnorm(1 - (1 - level) / 2) * sqrt(F_t_11[1,1])
    
    l_a_t_clt_00 = a_t_clt_00 - qnorm(1 - (1 - level) / 2) * sqrt(F_t_00[1,1])
    l_a_t_clt_10 = a_t_clt_10 - qnorm(1 - (1 - level) / 2) * sqrt(F_t_10[1,1])
    l_a_t_clt_01 = a_t_clt_01 - qnorm(1 - (1 - level) / 2) * sqrt(F_t_01[1,1])
    l_a_t_clt_11 = a_t_clt_11 - qnorm(1 - (1 - level) / 2) * sqrt(F_t_11[1,1])
    
    
    #-------------------#
    ### Hamilton part ###
    #-------------------#
    
    
    # Computes Pr(S_t = j, S_t-1 = i) conditional on information at time t-1
    # (t|t-1)
    Pr_clt_00 = q %*% Pr_clt_0
    Pr_clt_10 = (1 - p) %*% Pr_clt_1
    Pr_clt_01 = (1 - q) %*% Pr_clt_0
    Pr_clt_11 = p %*% Pr_clt_1
    
    # Pr of S_t = j conditional on t = t-1 is given by summarizing over all regimes at t = t-1
    # (t|t-1)
    Pr_clt_0 = Pr_clt_00 + Pr_clt_10
    Pr_clt_1 = Pr_clt_01 + Pr_clt_11
    
    # Records predicted probabilites 
    # (t|t-1)
    Prob_t_clt[i, 1] = Pr_clt_0
    Prob_t_clt[i, 2] = Pr_clt_1 #Two values are actually necessarry even though both probs add up to one, since some extremly small probs could be rounded to 1 and/ or zero
    
    
    #------------------------#
    ### Approximation part ###
    #------------------------#
    
    
    # Approximate values for State Vector and Var matrix to break exponential growth of required values
    a_t_clt_0 = (a_t_clt_00 %*% Pr_clt_00 + a_t_clt_10 %*% Pr_clt_10) %*% solve(Pr_clt_0)
    a_t_clt_1 = (a_t_clt_01 %*% Pr_clt_01 + a_t_clt_11 %*% Pr_clt_11) %*% solve(Pr_clt_1)
    
    # Also approximate prediction intervals
    u_a_t_clt_0 = (u_a_t_clt_00 %*% Pr_clt_00 + u_a_t_clt_10 %*% Pr_clt_10) %*% solve(Pr_clt_0)
    u_a_t_clt_1 = (u_a_t_clt_01 %*% Pr_clt_01 + u_a_t_clt_11 %*% Pr_clt_11) %*% solve(Pr_clt_1)
    
    l_a_t_clt_0 = (l_a_t_clt_00 %*% Pr_clt_00 + l_a_t_clt_10 %*% Pr_clt_10) %*% solve(Pr_clt_0)
    l_a_t_clt_1 = (l_a_t_clt_01 %*% Pr_clt_01 + l_a_t_clt_11 %*% Pr_clt_11) %*% solve(Pr_clt_1)
    
    Pr_clt_00 = as.numeric(Pr_clt_00)
    Pr_clt_10 = as.numeric(Pr_clt_10)
    Pr_clt_01 = as.numeric(Pr_clt_01)
    Pr_clt_11 = as.numeric(Pr_clt_11)
    
    Pr_clt_0  = as.numeric(Pr_clt_0)
    Pr_clt_1  = as.numeric(Pr_clt_1)
    
    P_t_clt_0 = ((Pr_clt_00 * (P_t_clt_00 + (a_t_clt_0 - a_t_clt_00) %*% t(a_t_clt_0 - a_t_clt_00))) + (Pr_clt_10 * (P_t_clt_10 + (a_t_clt_0 - a_t_clt_10) %*% t(a_t_clt_0 - a_t_clt_10)))) / Pr_clt_0
    P_t_clt_1 = ((Pr_clt_01 * (P_t_clt_01 + (a_t_clt_1 - a_t_clt_01) %*% t(a_t_clt_1 - a_t_clt_01))) + (Pr_clt_11 * (P_t_clt_11 + (a_t_clt_1 - a_t_clt_11) %*% t(a_t_clt_1 - a_t_clt_11)))) / Pr_clt_1
    
    # Approximate state vector and prediction intervals again to receive unconditional values
    a_t_clt = a_t_clt_0 * Pr_clt_0 + a_t_clt_1 * Pr_clt_1
    
    u_a_t_clt = u_a_t_clt_0 * Pr_clt_0 + u_a_t_clt_1 * Pr_clt_1
    l_a_t_clt = l_a_t_clt_0 * Pr_clt_0 + l_a_t_clt_1 * Pr_clt_1
    
    # Predict dependent variable
    y_t_clt = Z %*% a_t_clt
    
    
    #---------------------#
    ### Kalman part 2/2 ###
    #---------------------#
    
    
    # Store predicted values (t|t-1)
    a_clt_array[, 1, i] = a_t_clt_00
    a_clt_array[, 2, i] = a_t_clt_10
    a_clt_array[, 3, i] = a_t_clt_01
    a_clt_array[, 4, i] = a_t_clt_11
    
    P_clt_array[, 1:8, i]   = P_t_clt_00
    P_clt_array[, 9:16, i]  = P_t_clt_10
    P_clt_array[, 17:24, i] = P_t_clt_01
    P_clt_array[, 25:32, i] = P_t_clt_11
    
    y_clt_mat[i,] = y_t_clt[1,1]
    
    # Store approximated values (t|t)
    a_clt_approx_array[, 1, i] = a_t_clt_0
    a_clt_approx_array[, 2, i] = a_t_clt_1
    
    a_clt_approx_array[, 3, i] = u_a_t_clt_0
    a_clt_approx_array[, 4, i] = u_a_t_clt_1
    a_clt_approx_array[, 5, i] = l_a_t_clt_0
    a_clt_approx_array[, 6, i] = l_a_t_clt_1
    
    a_clt_approx_array[, 7, i] = a_t_clt
    
    a_clt_approx_array[, 8, i] = u_a_t_clt
    a_clt_approx_array[, 9, i] = l_a_t_clt
    
    P_clt_approx_array[, 1:8, i]  = P_t_clt_0
    P_clt_approx_array[, 9:16, i] = P_t_clt_1
    
    # Prediction step with approximated updates to complete loop (t+1|t)
    a_t_clt_00 = Tt %*% a_t_clt_0 + ew_00
    a_t_clt_10 = Tt %*% a_t_clt_1 + ew_10
    a_t_clt_01 = Tt %*% a_t_clt_0 + lambda + ew_01
    a_t_clt_11 = Tt %*% a_t_clt_1 + lambda + ew_11
    
    P_t_clt_00 = Tt %*% P_t_clt_0 %*% t(Tt) + R %*% (Q_0 + Q_Cov_00) %*% t(R)
    P_t_clt_10 = Tt %*% P_t_clt_1 %*% t(Tt) + R %*% (Q_0 + Q_Cov_10) %*% t(R)
    P_t_clt_01 = Tt %*% P_t_clt_0 %*% t(Tt) + R %*% (Q_1 + Q_Cov_01) %*% t(R)
    P_t_clt_11 = Tt %*% P_t_clt_1 %*% t(Tt) + R %*% (Q_1 + Q_Cov_11) %*% t(R)
    
  }
  
  # Output of filtered values
  return(list(a_clt        = a_clt_array,        
              P_clt        = P_clt_array,        
              a_clt_approx = a_clt_approx_array, 
              P_clt_approx = P_clt_approx_array, 
              Prob_clt     = Prob_t_clt,        
              y_clt        = y_clt_mat))        
  
}



###---------------------------------------------------------------------------------------------------------------------------------------------###
###---------------------------------------------------------------------------------------------------------------------------------------------###
### Application ###################################################################################################################################
###---------------------------------------------------------------------------------------------------------------------------------------------###
###---------------------------------------------------------------------------------------------------------------------------------------------###


par_ini_En_Nl_UC <- rep(0, 7)

# Final optimization
Model_En_Nl_UC <- optim(par_ini_En_Nl_UC, fn = Kim_likelihood_En_Nl_UC, hessian = T, method = "Nelder-Mead", control = list(maxit = 15000))

# Fitted model
Model_En_Nl_UC

# ML estimates
MLE_En_Nl_UC <- Model_En_Nl_UC$par %>% Par_constrain_En_Nl_UC()

# Use Hessian from MLE estimation to get the standard errors of estimates
MLE_SE_En_Nl_UC <- SEfromHessian(Model_En_Nl_UC$hessian, hessian = F, silent = F)


# Apply Kim filter & co
Filter_output_En_Nl_UC <- Kim_filter_En_Nl_UC(MLE_En_Nl_UC, data)

Smoother_output_En_Nl_UC <- Kim_Smoother_En_Nl_UC(MLE_En_Nl_UC, Filter_output_En_Nl_UC, 0.9)

Forecast_output <- Kim_forecast_En_Nl_UC(par = MLE_En_Nl_UC, 
                                         State_Vec = Filter_output_En_Nl_UC[[1]],
                                         State_Var = Filter_output_En_Nl_UC[[2]], 
                                         Prob_0 = Filter_output_En_Nl_UC[[5]][, 1],
                                         Prob_1 = Filter_output_En_Nl_UC[[5]][, 2], 0.5, 90)

# nu_0
Smoother_output_En_Nl_UC$a_cT[2, 1, T]
sqrt(Smoother_output_En_Nl_UC$P_cT[2, 2, T])


###---------------------------------------------------------------------------------------------------------------------------------------------###
###---------------------------------------------------------------------------------------------------------------------------------------------###
### Diagnostics ###################################################################################################################################
###---------------------------------------------------------------------------------------------------------------------------------------------###
###---------------------------------------------------------------------------------------------------------------------------------------------###

# Collect output
Trend <- tibble(Smooth0 = Smoother_output_En_Nl_UC[["a_cT"]][1, 1,], # Regime 0
                Smooth1 = Smoother_output_En_Nl_UC[["a_cT"]][1, 2,], # Regime 1
                Smooth3 = Smoother_output_En_Nl_UC[["a_cT"]][1, 3,], # Average
                Pr_0    = Smoother_output_En_Nl_UC[["Pr_cT"]][, 1],
                Pr_1    = Smoother_output_En_Nl_UC[["Pr_cT"]][, 2],
                Upper   = Smoother_output_En_Nl_UC[["a_CI_cT"]][1, 1,],
                Lower   = Smoother_output_En_Nl_UC[["a_CI_cT"]][1, 2,],
                Date = c(Covid$Date),
                Data = data) %>%
  mutate(index = 1:n(),
         Diff = Data - Smooth3)


# Smoothed trend with confidence intervals
Trend %>%
  ggplot() +
  geom_line(aes(x = index, y = Smooth3, colour = "Trend")) +
  geom_line(aes(x = index, y = Data, colour = "Data")) +
  geom_line(aes(x = index, y = Upper, colour = "Upper")) +
  geom_line(aes(x = index, y = Lower, colour = "Lower")) +
  theme_bw()

# Difference smoothed trend and actual data
Trend[-c(1:5),] %>%
  ggplot() +
  geom_line(aes(x = index, y = Diff)) +
  theme_bw()



# Smoothed trend and regime probabilities against actual data
colors <- c("Data" = "#FF6347", "Trend" = "#1874CD", "Pr regime 1" = "#757575")

# Figure 3
Trend %>%
  ggplot() +
  geom_line(aes(x = Date, y = Data, colour = "Data"), size = 0.7) +
  geom_line(aes(x = Date, y = Smooth3, colour = "Trend"), size = 1) +
  geom_line(aes(x = Date, y = Pr_1 * max(Data, na.rm = T), colour = "Pr regime 1"), size = 1) +
  scale_y_continuous(name = expression(paste(log, " ", I[t])), 
                     breaks = seq(0, 14, by = 2),
                     sec.axis = sec_axis(~.*(max(Trend$Pr_0, na.rm = T) / max(Trend$Data, na.rm = T)), 
                                         name = expression(paste(Pr, " ",S[t])==1), 
                                         breaks = seq(0, 1, by = 0.2)),
                     limits = c(0, max(Trend$Data, na.rm = T))) +
  scale_x_date(date_breaks = "3 months", date_labels = c("%m.%Y"), name = "") +
  theme_bw() +
  labs(colour = "") +
  scale_color_manual(values = colors) +
  theme(legend.position = "none",
        legend.text = element_text(size = 20),
        axis.text = element_text(size= 20),
        axis.title = element_text(size= 20, vjust = 1),
        panel.grid.major = element_blank(), panel.grid.minor = element_blank())


#---------------------------------------------------------------------------------------#
# Smoother, Regime and Forecast
#---------------------------------------------------------------------------------------#
n_ahead = 90

Forecast <- tibble(Data = c(data, rep(NA, n_ahead)), 
                   Trend = c(Trend$Smooth3, Forecast_output[[3]][1, 7,]),
                   Upper = c(rep(NA, length(data)), Forecast_output[[3]][1, 8,]),
                   Lower = c(rep(NA, length(data)), Forecast_output[[3]][1, 9,]),
                   Pr_1 = c(Smoother_output_En_Nl_UC[[3]][, 2], Forecast_output[[5]][, 2]),
                   Date = c(Covid$Date, seq(ymd(Covid$Date[nrow(Covid)]) + 1, ymd(Covid$Date[nrow(Covid)]) + n_ahead, by = 'days')))


colors <- c("Data" = "#FF6347", "Trend" = "#1874CD", "Pr regime 1" = "#757575")

# Smoothed trend, smoothed regime probabilites, forecasted trend and regime probabilites with prediction intervals against actual data
Forecast %>%
  ggplot() +
  geom_line(aes(x = Date, y = Data, colour = "Data"), size = 0.7) +
  geom_ribbon(aes(x = Date, ymin = Lower, ymax = Upper), alpha = 0.1) +
  geom_line(aes(x = Date, y = Trend, colour = "Trend"), size = 1) +
  geom_line(aes(x = Date, y = Pr_1 * max(Upper, na.rm = T), colour = "Pr regime 1"), size = 1) +
  scale_y_continuous(name = expression(log(I[t])), 
                     breaks = seq(0, 14, by = 2),
                     sec.axis = sec_axis(~.*(max(Forecast$Pr_1, na.rm = T) / max(Forecast$Upper, na.rm = T)), 
                                         name = expression(Pr(S[t] == 0)), 
                                         breaks = seq(0, 1, by = 0.2)),
                     limits = c(0, max(Forecast$Upper, na.rm = T))) +
  scale_x_date(date_breaks = "3 months", date_labels = c("%m.%Y"), name = "") +
  geom_vline(xintercept = Forecast$Date[T], linetype = "dashed", size = 1) +
  theme_bw() +
  labs(colour = "") +
  scale_color_manual(values = colors) +
  theme(legend.position = "bottom",
        legend.margin = margin(-15),
        legend.text = element_text(size = 20),
        axis.text = element_text(size = 20),
        axis.title = element_text(size = 20, vjust = 1),
        panel.grid.major = element_blank(), panel.grid.minor = element_blank())


# Transform estimates back into level values
Forecast_level <- Forecast %>%
  mutate(across(.cols = c(Trend, Data, Upper, Lower), .fns = exp))

Forecast_level %>%
  ggplot() +
  geom_line(aes(x = Date, y = Data, colour = "Data"), size = 0.7) +
  geom_ribbon(aes(x = Date, ymin = Lower, ymax = Upper), alpha = 0.1) +
  geom_line(aes(x = Date, y = Trend, colour = "Trend"), size = 1) +
  geom_line(aes(x = Date, y = Pr_1 * max(Upper, na.rm = T) * 0.6, colour = "Pr regime 1"), size = 1) +
  scale_y_continuous(name = expression(I[t]),
                     labels = scales::comma_format(big.mark = ".", decimal.mark = ","),
                     breaks = seq(0, 4e+06, 1e+06),
                     sec.axis = sec_axis(~.*(max(Forecast_level$Pr_1, na.rm = T) / max(Forecast_level$Upper, na.rm = T) / 0.6), 
                                         name = expression(paste(Pr, " ",S[t]==1)), 
                                         breaks = seq(0, 1, by = 0.2))) +
  scale_x_date(date_breaks = "3 months", date_labels = c("%m.%Y"), name = "") +
  geom_vline(xintercept = Forecast$Date[T], linetype = "dashed", size = 1) +
  theme_bw() +
  labs(colour = "") +
  scale_color_manual(values = colors) +
  theme(legend.position = "bottom",
        legend.margin = margin(-15),
        legend.text = element_text(size = 20),
        axis.text = element_text(size = 20),
        axis.title = element_text(size = 20, vjust = 1),
        panel.grid.major = element_blank(), panel.grid.minor = element_blank())


#---------------------------------------------------------------------------------------#
# Residuals
#---------------------------------------------------------------------------------------#

# Summarizes one-step-ahead prediction errors
Pred_err00 <- tibble(Date = Covid$Date,
                     Error = Filter_output_En_Nl_UC$Pred_err[,1],
                     type = "0 to 0",
                     Stddev = sd(Error, na.rm = T),
                     Mean = mean(Error, na.rm = T))

Pred_err10 <- tibble(Date = Covid$Date,
                     Error = Filter_output_En_Nl_UC$Pred_err[,2],
                     type = "1 to 0",
                     Stddev = sd(Error, na.rm = T),
                     Mean = mean(Error, na.rm = T))
Pred_err01 <- tibble(Date = Covid$Date,
                     Error = Filter_output_En_Nl_UC$Pred_err[,3],
                     type = "0 to 1",
                     Stddev = sd(Error, na.rm = T),
                     Mean = mean(Error, na.rm = T))
Pred_err11 <- tibble(Date = Covid$Date,
                     Error = Filter_output_En_Nl_UC$Pred_err[,4],
                     type = "1 to 1",
                     Stddev = sd(Error, na.rm = T),
                     Mean = mean(Error, na.rm = T))

Pred_err <- rbind(Pred_err00, Pred_err10, Pred_err01, Pred_err11) %>%
  arrange(Date, type)


v_plot <- Pred_err %>%
  ggplot() +
  geom_point(aes(x = Date, y = Error), size = 0.9) +
  geom_line(aes(x = Date, y =  (Mean + 2 * Stddev)), linetype = "dashed", color = "#1874CD", size = 1) +
  geom_line(aes(x = Date, y = (Mean - 2 * Stddev)), linetype = "dashed", color = "#1874CD", size = 1) +
  facet_wrap(~ type,
             labeller = label_bquote(paste(S[t-1], " = ", .(substr(type, 1, 1)), ", ", 
                                           S[t], " = ", .(substr(type, 6, 6))))) +
  theme_bw() +
  scale_y_continuous(name = expression(v[t]),
                     breaks = seq(-1.5, 1.5, 1.5)) +
  scale_x_date(date_breaks = "6 months", date_labels = c("%b"), name = "") +
  theme(legend.position = "bottom",
        strip.text = element_text(size = 20),
        axis.text = element_text(size = 20),
        axis.title = element_text(size = 20, vjust = 1),
        panel.grid.major = element_blank(), 
        panel.grid.minor = element_blank())



# ACF of residuals
CI_interval <- 0.95

ACF_00 <- tibble(AC = acf(Pred_err00$Error)$acf[-1, 1, 1],
                 CI = qnorm((1 + CI_interval) / 2) / sqrt(acf(Pred_err00$Error)$n.used),
                 type = Pred_err00$type[1]) %>%
  mutate(Lags = 1:n())

ACF_10 <- tibble(AC = acf(Pred_err10$Error)$acf[-1, 1, 1],
                 CI = qnorm((1 + CI_interval) / 2) / sqrt(acf(Pred_err00$Error)$n.used),
                 type = Pred_err10$type[1]) %>%
  mutate(Lags = 1:n())

ACF_01 <- tibble(AC = acf(Pred_err01$Error)$acf[-1, 1, 1],
                 CI = qnorm((1 + CI_interval) / 2) / sqrt(acf(Pred_err00$Error)$n.used),
                 type = Pred_err01$type[1]) %>%
  mutate(Lags = 1:n())

ACF_11 <- tibble(AC = acf(Pred_err11$Error)$acf[-1, 1, 1],
                 CI = qnorm((1 + CI_interval) / 2) / sqrt(acf(Pred_err00$Error)$n.used),
                 type = Pred_err11$type[1]) %>%
  mutate(Lags = 1:n())

ACF <- rbind(ACF_00, ACF_10, ACF_01, ACF_11) %>%
  arrange(Lags, type)



ACF_plot <- ACF %>%
  ggplot() +
  geom_bar(aes(x = Lags, y = AC), stat = "identity", width = 0.5) +
  geom_line(aes(x = Lags, y = CI), linetype = "dashed", color = "#1874CD", size = 1) +
  geom_line(aes(x = Lags, y = -CI), linetype = "dashed", color = "#1874CD", size = 1) +
  geom_hline(yintercept = 0) +
  facet_wrap(~ type,
             labeller = label_bquote(paste(S[t-1], " = ", .(substr(type, 1, 1)), ", ", 
                                           S[t], " = ", .(substr(type, 6, 6))))) +
  theme_bw() +
  scale_y_continuous(breaks = seq(-0.1, 0.1, 0.1)) +
  labs(y = expression(paste("ACF ", v[t]))) +
  scale_x_continuous(breaks = seq(0, 25, by = 5)) +
  theme(legend.position = "bottom",
        strip.text = element_text(size = 20),
        axis.text = element_text(size = 20),
        axis.title = element_text(size = 20, vjust = 1),
        panel.grid.major = element_blank(), panel.grid.minor = element_blank())

# Figure 5
ggpubr::ggarrange(v_plot, ACF_plot, nrow = 1)


#---------------------------------------------------------------------------------------#
# Seasonality
#---------------------------------------------------------------------------------------#

Season <- tibble(Season = Smoother_output_En_Nl_UC$a_cT[3,3,],
                 Date = Covid$Date) %>%
  slice(-T)

Season %>%
  ggplot() +
  geom_line(aes(x = Date, y = Season)) +
  scale_x_date(date_breaks = "3 months", date_labels = c("%m.%Y"), name = "") +
  theme_bw() +
  scale_y_continuous(name = expression(gamma[t]), breaks = seq(-1, 1, 0.5)) +
  ylim(-1, 1) +
  theme(legend.position = "bottom",
        legend.margin = margin(-15),
        legend.text = element_text(size = 20),
        axis.text = element_text(size = 20),
        axis.title = element_text(size = 20, vjust = 1),
        panel.grid.major = element_blank(), panel.grid.minor = element_blank())



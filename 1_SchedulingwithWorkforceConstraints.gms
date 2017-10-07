* Lean.gms
*
$eolcom //
option iterlim=999999999;     // avoid limit on iterations
option reslim=300;            // timelimit for solver in sec.
option optcr=0.0;             // gap tolerance
option solprint=ON;           // include solution print in .lst file
option limrow=10000;            // limit number of rows in .lst file
option limcol=10000;            // limit number of columns in .lst file
*------------------------------------------------------------------------

sets
         jobs    'jobs'          /1*15/
         weeks   'weeks'         /1*23/
         skills  'skills'        /1*3/;

alias    (jobs,j,k);
alias    (weeks,t,u);
alias    (skills,i)


parameter
         p(j)            'processing time of job j in weeks'
/        1       1
         2       2
         3       2
         4       3
         5       1
         6       2
         7       1
         8       3
         9       1
         10      1
         11      1
         12      2
         13      2
         14      1
         15      0       /     ;

parameter
         r(i)            'number of people available of skill i'
        /1       2
         2       2
         3       2       /      ;



table
         w(i,j)          'nº of persons of skill i necessary for job j'
                 1       2       3       4       5       6       7       8       9       10      11      12      13      14      15
         1       2       0       2       1       2       0       2       0       1       2       2       0       2       0       0
         2       2       1       1       1       2       0       1       2       1       2       2       0       2       1       0
         3       2       2       0       0       2       1       1       0       1       1       2       1       1       1       0       ;



table
         s(j,k)          '1 if job j followed by job k'
         1       2       3       4       5       6       7       8       9       10      11      12      13      14      15
1        0       1       0       0       0       0       0       0       0       0       0       0       0       0       1
2        0       0       1       0       0       1       0       0       0       0       0       0       0       0       1
3        0       0       0       1       0       0       0       1       0       0       0       0       0       0       1
4        0       0       0       0       1       0       0       0       0       0       0       0       0       0       1
5        0       0       0       0       0       0       1       1       0       0       0       0       0       0       1
6        0       0       0       0       0       0       0       0       0       0       0       1       0       0       1
7        0       0       0       0       0       0       0       0       0       1       0       0       0       0       1
8        0       0       0       0       0       0       0       0       1       0       0       0       0       0       1
9        0       0       0       0       0       0       0       0       0       1       0       0       0       0       1
10       0       0       0       0       0       0       0       0       0       0       1       0       0       0       1
11       0       0       0       0       0       0       0       0       0       0       0       0       1       0       1
12       0       0       0       0       0       0       0       0       0       0       0       0       0       1       1
13       0       0       0       0       0       0       0       0       0       0       0       0       0       1       1
14       0       0       0       0       0       0       0       0       0       0       0       0       0       0       1
15       0       0       0       0       0       0       0       0       0       0       0       0       0       0       1   ;

scalar
         H               'upper bound of makespan'       /23/;


binary variable


         x(j,t)          '1 if job j completed at time t, 0 otherwise.';
variable
         z               'makespan';

equations
         makespan                'objective function'
         precedence(j,k)           'ensure precedence happens'
         availability(i,t)       'ensure availability is respected'
         process(j)              'process every job';

makespan..               z =e= sum(t,ord(t)*x('15',t));

precedence(j,k)..        s(j,k)*(sum(t,ord(t)*x(j,t))+p(k)-sum(t,ord(t)*x(k,t))) =l= 0;

*availability(i,t)..      sum(j,w(i,j)*sum(u$(ord(u)<(ord(t)+p(j)-1) and ord(u)=ord(t)),x(j,u))) =l= r(i);

availability(i,t)..      sum(j,w(i,j)*sum[u$(ord(u)=ord(t) and ord(u)<(ord(t)+p(j)-1) ),x(j,u)]) =l= r(i);




process(j)..             sum(t,x(j,t))=e=1;

model lean /all/;

Solve lean using mip minimizing z ;

// the variables which forms the solution:
display p;
display w;
DISPLAY x.L;
DISPLAY z.L;


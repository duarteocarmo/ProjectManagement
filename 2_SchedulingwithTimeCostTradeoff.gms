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
         skills  'skills'        /1*3/;

alias    (jobs,j,k);
alias    (skills,i)


parameter
         fp(j)            'processing time of job j in weeks'
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

parameter pmax(j);
parameter pmin(j);

pmax(j)=fp(j)+1;
pmin(j)=fp(j);


parameter cw(i)          'cost of a week for worker of type i'
/        1       10250
*DEVELOPER
         2       9000
*DESIGNER
         3       11000   /;
*MANAGER



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


parameter c(j);

c(j)=sum(i,w(i,j)*cw(i));



scalar
         c0              'fixed overhead cost per unit of time'  /121000/;

variable x(j);
variable cmax;
variable p(j);
variable z;

equations
         goalhere
         maximum(j)
         minimum(j)
         precedence(j,k)
         positivity(j)
         itallends(j);

goalhere..                       z=e= c0*cmax-sum(j,c(j)*p(j));

maximum(j)..                     p(j)=l=pmax(j);

minimum(j)..                     p(j)=g=pmin(j);

precedence(j,k)..                s(j,k)*(x(k)-p(j)-x(j))=g=0;

positivity(j)..                  x(j)=g=0;

itallends(j)..                   cmax-x(j)-p(j)=g=0;

model pas /all/;

Solve pas using mip minimizing z;

display c;
display c0;
display pmax;
display fp;
display pmin;
display x.L;
display cmax.L;
display p.L;
display z.L;

parameter diffp(j);

diffp(j)=p.L(j)-fp(j);

display diffp;



$ontext

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

availability(i,t)..      sum(j,w(i,j)*sum(u$(ord(u)<(ord(t)+p(j)-1) and ord(u)>ord(t)),x(j,u))) =l= r(i);

process(j)..             sum(t,x(j,t))=e=1;

model lean /all/;

Solve lean using mip minimizing z ;

// the variables which forms the solution:
DISPLAY x.L;
DISPLAY z.L;

$offtext

#define Fork byte
#define Hand byte
#define N 5  			/* number of philosophers and forks */

Fork forks[N] = 1;
int eating = 0;  		/* counts the number of philosophers eating  */


ltl deadlock_free { []<> (eating > 0) };

proctype Philo(int i) {
  /* corresponds to the i_th philosopher */
  Hand right = 0;
  Hand left = 0;

  do
  :: atomic{ forks[i%N] && !left -> forks[i%N]--; left++;
     if	                       	/* we check if the philosopher has both forks */
     :: (right) -> eating++
     :: (!right) -> skip
     fi
     }                         /* taking fork */
  :: atomic{ forks[(i+1)%N] && !right -> forks[(i+1)%N]--; right++
     if                        /* we check if the philosopher has both forks */
     :: (left) -> eating++
     :: (!left) -> skip
     fi
     }                         /* taking fork */
  :: atomic{ left && right -> left--; right--; forks[i%N]++; forks[(i+1)%N]++; eating-- }    /* After eating, giving forks back */
  od;

}

init {
     run Philo(0);
     run Philo(1);
     run Philo(2);
     run Philo(3);
     run Philo(4);
}
    
  
/*

We put "atomic" to avoid cases where 2 philosopher see a free fork and try to take it "at the same time".

Running this with verfification find an error trail.
Running the error trail gives an execution where each philosopher has a fork:

 Philo(1):left  =  1
 Philo(2):left  =  1
 Philo(3):left  =  1
 Philo(4):left  =  1
 Philo(5):left  =  1
 eating  =  0
 forks[0]  =  0
 forks[1]  =  0
 forks[2]  =  0
 forks[3]  =  0
 forks[4]  =  0

*/

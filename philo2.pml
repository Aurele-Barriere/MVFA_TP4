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
  :: atomic{ forks[i%N] && !left && ( right || i%N < (i+1)%N ) -> forks[i%N]--; left++;
     if	                       	/* we check if the philosopher has both forks */
     :: (right) -> eating++
     :: (!right) -> skip
     fi
     }                         /* taking fork */
  :: atomic{ forks[(i+1)%N] && !right && ( left || (i+1)%N < i%N ) -> forks[(i+1)%N]--; right++
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

In this file, we implement Dijsktra Resource hierarchy solution ( https://en.wikipedia.org/wiki/Dining_philosophers_problem#Resource_hierarchy_solution )


Basically, each fork is given a number (in our case, it's index in the array).
Philosophers only take their lowest fork first.

Which means that a philosopher can take the fork to its right if
      - the right fork is available and their right hand is free   and
      	    - either they already have another fork in their left hand
	    - either the right fork is lower than the left fork


It prevents them from taking each one fork because the highest one cannot be taken as a first fork.

Indeed, after executing the verification tool, we have 

Full statespace search for:
	never claim         	+ (deadlock_free)
	assertion violations	+ (if within scope of claim)
	acceptance   cycles 	+ (fairness disabled)
	invalid end states	- (disabled by never claim)

No errors found -- did you verify all claims?


Which means that a deadlock is impossible in this implementation.

*/

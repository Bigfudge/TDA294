#define NUM_PHIL 5

bool forks[NUM_PHIL];

proctype phil(int id) {
  do
    :: printf("Philosopher %d is thinking\n", id);

       /* Deduce which forks are ours */
       int leftfork = id;
       int rightfork = id+1;

       /* % is not a thing in SPIN? */
       if
         :: id+1 >= NUM_PHIL -> rightfork = 0;
         :: else -> rightfork = id+1;
       fi
       assert(rightfork < NUM_PHIL);

       /* Start acquiring forks */
       bool leftforkacquired = false;
       bool rightforkacquired = false;
       do
          :: leftforkacquired && rightforkacquired -> break
          :: !leftforkacquired || !rightforkacquired ->
            /* Acquire left fork first */
            atomic {
              do
                :: !forks[leftfork] ->
                   forks[leftfork] = true;
                   leftforkacquired = true;

                :: leftforkacquired -> break
              od
            }

            /* Acquire right fork */
            atomic {
              if
                /* Right fork is usable */
                :: !forks[rightfork] ->
                   forks[rightfork] = true;
                   rightforkacquired = true;

                /* Right fork is unusable, release left for and restart */
                :: else ->
                   forks[leftfork] = false;
                   leftforkacquired = false;
              fi
            }
       od
       assert(leftforkacquired && rightforkacquired);
       assert(forks[leftfork] && forks[rightfork]);

       /* Eat */
       printf("Philosopher %d is eating with forks %d and %d\n", id, leftfork, rightfork);

       /* Return forks */
       forks[rightfork] = false;
       forks[leftfork] = false;
  od
}

init  {
  int i = 0;

  do
    :: i >= NUM_PHIL -> break
    :: else -> run phil(i);
               i++
  od
}

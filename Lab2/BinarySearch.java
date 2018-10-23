public class BinarySearch {

	private /*@nullable@*/ int[] numbers;
	
	/* size is the number of used positions in the array (since the list of numbers will become shorter when removing duplicates) */
	private /*@spec_public@*/ int size;
	
	private /*@spec_public@*/ int query;

	public BinarySearch(int[] numbers, int query) {
		this.numbers = numbers;
		this.size = numbers.length - 1;
		this.query = query;
		performBinarySearch();
	}

	/*@
	  @ public normal_behavior
	  @ requires (\forall int i; i>=0 && i<numbers.length; numbers[i] == 1);
	  @ ensures numbers != null;
	  @*/
	public void report(String message) {
		// print the message...
		return;
	}


	/*@
	  @ public normal_behavior
	  @ requires numbers != null;
	  @ requires (\forall int p, j; p >= 0 && p < j && j <= size; numbers[p] <= numbers[j]);
	  @ requires (\exists int q; q >= 0 && q <= size; numbers[q] == query);
	  @ ensures \result != -1 && numbers[\result] == query;
	  @*/
	public int performBinarySearch() {
report("Eliminating duplicates.");
		eliminateDuplicates(numbers);
		report("Searching for " + query);
		int searchResult = search();
		return searchResult;
	}

	

	/*@
	  @ public normal_behavior
	  @ requires numbers != null;
	  @ requires (\forall int i, j; i >= 0 && i < j && j <= size; numbers[i] <= numbers[j]);
	  @ ensures (\forall int e;
          @         (\exists int i; 0 <= i && i <= size; numbers[i] == e) <==>
          @	    (\exists int i; 0 <= i && i <= \old(size); \old(numbers)[i] == e));
	  @ ensures (\forall int i, j; i >= 0 && i < j && j <= size; numbers[i] < numbers[j]);
	  @ ensures numbers != null;
	  @ assignable numbers, size;
	  @
	  @ also
	  @
	  @ public exceptional_behaviour
 	  @ requires numbers.length == 0 && numbers != null;
          @ signals_only RuntimeException;
          @ signals (RuntimeException) size == -1;
	  @ assignable size;
	  @*/
	private void eliminateDuplicates(int[] numbers) {
    // Implement exceptional_behaviour case
    if (numbers != null && numbers.length == 0) {
      this.size = -1;
      throw new RuntimeException("");
    }
		int i = 0;
		while (i < numbers.length - 1) {
			if (i >= size)
				break;
			if (numbers[i] == numbers[i + 1]) {
				int j = i + 1;
				while (j < numbers.length - 1) {
					numbers[j] = numbers[j + 1];
					j++;
				}
				numbers[numbers.length - 1] = 0;
				size--;
			}
			i++;
		}
	}

	/*@
	  @ public normal_behavior
	  @ requires numbers != null;
	  @ requires (\forall int m,j; m >= 0 && m < j && j <= size; numbers[m] < numbers[j]);
	  @ requires (\exists int n; 0 <= n && n <= size; numbers[n] == query);
	  @ ensures \result != -1 && numbers[\result] == query;
	  @ assignable \nothing;
	  @
	  @ also
	  @
	  @ public normal_behavior
	  @ requires (\forall int i,j; i >= 0 && i < j && j <= size; numbers[i] < numbers[j]);
	  @ requires (\forall int i; i >= 0 && i <= size; numbers[i] != query);
	  @ ensures \result == -1;
	  @ assignable \nothing;
	  @
	  @ also
	  @
	  @ public exceptional_behaviour
	  @ requires (\exists int i,j; i >= 0 && i < j && j <= size; numbers[i] > numbers[j] || numbers[i] == numbers[j]);
	  @ signals_only RuntimeException;
	  @ assignable \nothing;
	  @*/
	private int search() {
		int leftIndex = 0;
		int rightIndex = size;

		while (leftIndex <= rightIndex) {
			int index = leftIndex + ((rightIndex - leftIndex) / 2);
			if (numbers[index] < query) {
				leftIndex = index + 1;
			} else if (numbers[index] > query) {
				rightIndex = index - 1;
			} else {
				return index;
			}
		}

		return -1;
	}

}

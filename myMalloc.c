#include <errno.h>
#include <pthread.h>
#include <stddef.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>

#include "myMalloc.h"
#include "printing.h"

/* Due to the way assert() prints error messges we use out own assert function
 * for deteminism when testing assertions
 */
#ifdef TEST_ASSERT
  inline static void assert(int e) {
    if (!e) {
      const char * msg = "Assertion Failed!\n";
      write(2, msg, strlen(msg));
      exit(1);
    }
  }
#else
  #include <assert.h>
#endif

/*
 * Mutex to ensure thread safety for the freelist
 */
static pthread_mutex_t mutex;

/*
 * Array of sentinel nodes for the freelists
 */
header freelistSentinels[N_LISTS];

/*
 * Pointer to the second fencepost in the most recently allocated chunk from
 * the OS. Used for coalescing chunks
 */
header * lastFencePost;

/*
 * Pointer to maintian the base of the heap to allow printing based on the
 * distance from the base of the heap
 */ 
void * base;

/*
 * List of chunks allocated by  the OS for printing boundary tags
 */
header * osChunkList [MAX_OS_CHUNKS];
size_t numOsChunks = 0;

/*
 * direct the compiler to run the init function before running main
 * this allows initialization of required globals
 */
static void init (void) __attribute__ ((constructor));

// Helper functions for manipulating pointers to headers
static inline header * get_header_from_offset(void * ptr, ptrdiff_t off);
static inline header * get_left_header(header * h);
static inline header * ptr_to_header(void * p);


void insert_into_freelist(header *block, int index);
int get_index(header *block); 


// Helper functions for allocating more memory from the OS
static inline void initialize_fencepost(header * fp, size_t left_size);
static inline void insert_os_chunk(header * hdr);
static inline void insert_fenceposts(void * raw_mem, size_t size);
static header * allocate_chunk(size_t size);

// Helper functions for freeing a block
static inline void deallocate_object(void * p);

// Helper functions for allocating a block
static inline header * allocate_object(size_t raw_size);

// Helper functions for verifying that the data structures are structurally 
// valid
static inline header * detect_cycles();
static inline header * verify_pointers();
static inline bool verify_freelist();
static inline header * verify_chunk(header * chunk);
static inline bool verify_tags();

static void init();

static bool isMallocInitialized;

/**
 * @brief Helper function to retrieve a header pointer from a pointer and an 
 *        offset
 *
 * @param ptr base pointer
 * @param off number of bytes from base pointer where header is located
 *
 * @return a pointer to a header offset bytes from pointer
 */
static inline header * get_header_from_offset(void * ptr, ptrdiff_t off) {
	return (header *)((char *) ptr + off);
}

/**
 * @brief Helper function to get the header to the right of a given header
 *
 * @param h original header
 *
 * @return header to the right of h
 */
header * get_right_header(header * h) {
	return get_header_from_offset(h, get_size(h));
}

/**
 * @brief Helper function to get the header to the left of a given header
 *
 * @param h original header
 *
 * @return header to the right of h
 */
inline static header * get_left_header(header * h) {
  return get_header_from_offset(h, -h->left_size);
}

/**
 * @brief Fenceposts are marked as always allocated and may need to have
 * a left object size to ensure coalescing happens properly
 *
 * @param fp a pointer to the header being used as a fencepost
 * @param left_size the size of the object to the left of the fencepost
 */
inline static void initialize_fencepost(header * fp, size_t left_size) {
	set_state(fp,FENCEPOST);
	set_size(fp, ALLOC_HEADER_SIZE);
	fp->left_size = left_size;
}

/**16
 * @brief Helper function to maintain list of chunks from the OS for debugging
 *
 * @param hdr the first fencepost in the chunk allocated by the OS
 */
inline static void insert_os_chunk(header * hdr) {
  if (numOsChunks < MAX_OS_CHUNKS) {
    osChunkList[numOsChunks++] = hdr;
  }
}

/**
 * @brief given a chunk of memory insert fenceposts at the left and 
 * right boundaries of the block to prevent coalescing outside of the
 * block
 *
 * @param raw_mem a void pointer to the memory chunk to initialize
 * @param size the size of the allocated chunk
 */
inline static void insert_fenceposts(void * raw_mem, size_t size) {
  // Convert to char * before performing operations
  char * mem = (char *) raw_mem;

  // Insert a fencepost at the left edge of the block
  header * leftFencePost = (header *) mem;
  initialize_fencepost(leftFencePost, ALLOC_HEADER_SIZE);

  // Insert a fencepost at the right edge of the block
  header * rightFencePost = get_header_from_offset(mem, size - ALLOC_HEADER_SIZE);
  initialize_fencepost(rightFencePost, size - 2 * ALLOC_HEADER_SIZE);
}

/**
 * @brief Allocate another chunk from the OS and prepare to insert it
 * into the free list
 *
 * @param size The size to allocate from the OS
 *
 * @return A pointer to the allocable block in the chunk (just after the 
 * first fencpost)
 */
static header * allocate_chunk(size_t size) {
  void * mem = sbrk(size);
  
  insert_fenceposts(mem, size);
  header * hdr = (header *) ((char *)mem + ALLOC_HEADER_SIZE);
  set_state(hdr, UNALLOCATED);
  set_size(hdr, size - 2 * ALLOC_HEADER_SIZE);
  hdr->left_size = ALLOC_HEADER_SIZE;
  return hdr;
}

// Correctly insert the header/block passed into the freelist
void insert_into_freelist(header *block, int index) {
  header *freelist = &freelistSentinels[index];
  freelist->next->prev = block;
  block->prev = freelist;
  block->next = freelist->next;
  freelist->next = block;
  return;
}

/**
 * @brief Helper allocate an object given a raw request size from the user
 *
 * @param raw_size number of bytes the user needs
 *
 * @return A block satisfying the user's request
 */
static inline header * allocate_object(size_t raw_size) {
  if (raw_size == 0)
    return NULL;
  // Calculate the rounded up raw_size to the multiple of 8
  size_t rem8 = 8 - raw_size % 8;
  size_t sizeRoundedTo8 = raw_size;
  if (rem8 < 8)
    sizeRoundedTo8 = raw_size + rem8;
  if (sizeRoundedTo8 < 16)
    sizeRoundedTo8 = 16;
  int ilist = sizeRoundedTo8/8 - 1;
  if (ilist >= N_LISTS)
    ilist = N_LISTS - 1;
  header *freelist = NULL;
  int i = 0;

  // Finding a non-empty list
  for (i = ilist; i < N_LISTS; i++) {
    freelist = &freelistSentinels[i];
    if (freelist->next != freelist)
      break;
  }

  // Seeing if we are at the end of the freelist
  if (i == N_LISTS - 1) {
    size_t totalsize = sizeRoundedTo8 + ALLOC_HEADER_SIZE;
    header *new_list = &freelistSentinels[i];
    header *temp = new_list;
    while (temp->next != new_list) {
      if (get_size(temp->next) >= totalsize) {
        temp = temp->next;
        break;
      }
      temp = temp->next;
    }
    if (temp == new_list) {
      i = N_LISTS;
    }
    else {
      header *h1 = temp;
      header *h2 = get_header_from_offset(h1, get_size(h1) - totalsize);
      // Checking if the blocka are of the exact size
      if (get_size(h1) - totalsize < (2 * ALLOC_HEADER_SIZE)) {
        // Remove h1 from freelist
        h1->prev->next = h1->next;
        h1->next->prev = h1->prev;
        set_state(h1, ALLOCATED);
        return (header *) h1->data;
      }
      else {
        // Spliting the block
        int rem_size = get_size(h1) - totalsize;
        set_size(h1, rem_size);
        set_size(h2, totalsize);
        set_state(h2, ALLOCATED);
        if (get_size(h1) < (ALLOC_HEADER_SIZE + (N_LISTS * MIN_ALLOCATION))) {
          // Remove h1 from freelist
          h1->prev->next = h1->next;
          h1->next->prev = h1->prev;
          int index = get_index(h1);
          insert_into_freelist(h1, index);
          // Set the appropriate left_size for the right's right-block
          header * righth2 = get_right_header(h2);
          righth2->left_size = totalsize;
          h2->left_size = get_size(h1);
          return (header *)h2->data;
        }
        // Set the appropriate left_size for the right's right-block
        header * righth2 = get_right_header(h2);
        righth2->left_size = totalsize;
        h2->left_size = get_size(h1);
        return (header *)h2->data;
      }
    }
  }

  // ilist is out of the N_LISTS bound
  if (i == N_LISTS) {
    // Handle not enough memory
    // old block | last fencepost | left fencepost | new chunck | right fencepost |
    header *new_block = allocate_chunk(ARENA_SIZE);
    header *left_fencepost_nb = get_header_from_offset(new_block, -ALLOC_HEADER_SIZE);
    header *right_fencepost_nb = get_header_from_offset(new_block, get_size(new_block));
    // last fencepost of the prev chunck
    header *last_fencepost_prev = get_header_from_offset(left_fencepost_nb, -ALLOC_HEADER_SIZE);

    // If 2 chuncks are adjacents
    if (last_fencepost_prev == lastFencePost) {
      header *old_block = get_left_header(last_fencepost_prev);
      // If the block before the last_fencepost_prev is ALLOCATED
      if (get_state(old_block) == ALLOCATED) {
        size_t size = get_size(new_block) + (2 * ALLOC_HEADER_SIZE);
        set_size(last_fencepost_prev, size);
        set_state(last_fencepost_prev, UNALLOCATED);
        right_fencepost_nb->left_size = get_size(last_fencepost_prev);
        int index = get_index(last_fencepost_prev);
        insert_into_freelist(last_fencepost_prev, index);
        // Update lastFencePost
        lastFencePost = right_fencepost_nb;
        return allocate_object(raw_size);
      }
      // If the block before the last_fencepost_prev is UNALLOCATED 
      else {
        int oldindex = get_index(old_block);
        size_t size = get_size(old_block) + get_size(new_block) + (2 * ALLOC_HEADER_SIZE);
        set_size(old_block, size);
        set_state(old_block, UNALLOCATED);
        right_fencepost_nb->left_size = get_size(old_block);
        // If oldindex is not the last block in the freelist
        if (oldindex != N_LISTS - 1) {
          old_block->prev->next = old_block->next;
          old_block->next->prev = old_block->prev;
          int index = get_index(old_block);
          insert_into_freelist(old_block, index);
        }
        // Update lastFencePost
        lastFencePost = right_fencepost_nb;
        return allocate_object(raw_size);
      }
    }
    // If the 2 chunks are not adjacent 
    else {
      // Insert into freelist if new block is not already in the freelist
      int index = get_index(new_block);
      insert_into_freelist(new_block, index);
      lastFencePost = right_fencepost_nb;
      // Insert old block into os chunk
      insert_os_chunk(left_fencepost_nb);
      return allocate_object(raw_size);
    }
  }
  // We countinue here if ilist is not at the end of the freelist
  // Calculate totalsize of the block with the header size
  size_t totalsize = sizeRoundedTo8 + ALLOC_HEADER_SIZE;
  header *h1 = freelist->next;
  header *h2 = get_header_from_offset(h1, get_size(h1) - totalsize);
  if (get_size(h1) - totalsize < (2 * ALLOC_HEADER_SIZE)) {
    // Remove h1 from freelist
    h1->prev->next = h1->next;
    h1->next->prev = h1->prev;
    set_state(h1, ALLOCATED);
    // Set the appropriate left_size for the h1's right-block
    header *h3 = get_right_header(h1);
    h3->left_size = get_size(h1);
    return (header *) h1->data;
  }
  else {
    int rem_size = get_size(h1) - totalsize;
    set_size(h1, rem_size);
    set_size(h2, totalsize);
    set_state(h2, ALLOCATED);
    // Remove from freelist
    h1->prev->next = h1->next;
    h1->next->prev = h1->prev;
    int index = get_index(h1);
    insert_into_freelist(h1, index);
    // Set the appropriate left_size for the h2's right-block
    header * righth2 = get_right_header(h2);
    righth2->left_size = totalsize;
    h2->left_size = get_size(h1);
    return (header *)h2->data;
  }
}

/**
 * @brief Helper to get the header from a pointer allocated with malloc
 *
 * @param p pointer to the data region of the block
 *
 * @return A pointer to the header of the block
 */
static inline header * ptr_to_header(void * p) {
  return (header *)((char *) p - ALLOC_HEADER_SIZE); //sizeof(header));
}

// Returns the correct index of the block with comparsion with 
// the freelist
int get_index(header *block) {
  int index = ((get_size(block) - ALLOC_HEADER_SIZE)/8) - 1;
  if (index > N_LISTS - 1)
    index = N_LISTS - 1;
  return index;
}

/**
 * @brief Helper to manage deallocation of a pointer returned by the user
 *
 * @param p The pointer returned to the user by a call to malloc
 */
static inline void deallocate_object(void * p) {
  if (p == NULL)
    return;
  header *block = ptr_to_header(p);
  // Double Detection
  if(get_state(block) == UNALLOCATED) {
    fprintf(stderr, "Double Free Detected\n");
    assert(false);
    exit(1);
  }
  else {
    set_state(block, UNALLOCATED);
  }
  header * left = get_left_header(block);
  header * right = get_right_header(block);
  // If left and right block is ALLOCATED
  if (get_state(left) != UNALLOCATED && get_state(right) != UNALLOCATED) {
    // Simply insert the block into the freelist
    size_t index = get_index(block);
    insert_into_freelist(block, index);
    set_state(block, UNALLOCATED);
  }
  // If left and right block are UNALLOCATED
  else if (get_state(left) == UNALLOCATED && get_state(right) == UNALLOCATED) {
    int oldleftindex = get_index(left);
    // Setting the size of the left to its new size as the coalasce should
    // happen on the left block
    size_t size = get_size(block) + get_size(left) + get_size(right);
    set_size(left, size);
    // Setting the left size of the right's right block
    header * right_right = get_right_header(right);
    right_right->left_size = get_size(left);
    set_state(left, UNALLOCATED);
    // Remove right block from the freelist
    right->prev->next = right -> next;
    right->next->prev = right -> prev;
    // If left index is not at the end of the freelist
    if (oldleftindex != N_LISTS - 1) {
      // Remove left block the freelist
      left->prev->next = left->next;
      left->next->prev = left->prev;
      // Insert the left block correctly into the freelist
      size_t index = get_index(left);
      insert_into_freelist(left, index);
    }
  }
  // If right block is UNALLOCATED
  else if (get_state(right) == UNALLOCATED && get_state(left) != UNALLOCATED) {
    // Setting the size of the current block to its new size as the coalasce should
    // happen on the current block
    size_t size = get_size(block) + get_size(right);
    set_size(block, size);
    // Setting the left size of the right's right block
    header * right_right = get_right_header(right);
    right_right->left_size = get_size(block);
    set_state(block, UNALLOCATED);
    size_t index = get_index(block);
    // Remove right block from the freelist 
    right->prev->next = right->next;
    right->next->prev = right->prev;
    // Inserting the updated block at the correct index in the freelist
    insert_into_freelist(block, index);
  }
  // If both left block is UNALLOCATED
  else if(get_state(right) != UNALLOCATED && get_state(left) == UNALLOCATED) {
    int oldleftindex = get_index(left);
    // Setting the size of the current block to its new size as the coalasce should
    // happen on the left block
    size_t size = get_size(block) + get_size(left);
    set_size(left, size);
    set_state(left, UNALLOCATED);
    // Setting the right block's left size to the new size of left 
    right->left_size = get_size(left);
    // If left index is not at the end of the freelist
    if (oldleftindex != N_LISTS - 1) {
        // Remove the left block from the freelist
        left->prev->next = left->next;
        left->next->prev = left->prev;
        // Insert the left correctly into the freelist
        size_t index = get_index(left);
        insert_into_freelist(left, index);
        // left->next->left_size = get_size(left);
    }
  }
  return;
}

/**
 * @brief Helper to detect cycles in the free list
 * https://en.wikipedia.org/wiki/Cycle_detection#Floyd's_Tortoise_and_Hare
 *
 * @return One of the nodes in the cycle or NULL if no cycle is present
 */
static inline header * detect_cycles() {
  for (int i = 0; i < N_LISTS; i++) {
    header * freelist = &freelistSentinels[i];
    for (header * slow = freelist->next, * fast = freelist->next->next;
         fast != freelist;
         slow = slow->next, fast = fast->next->next) {
      if (slow == fast) {
        return slow;
      }
    }
  }
  return NULL;
}

/**
 * @brief Helper to verify that there are no unlinked previous or next pointers
 *        in the free list
 *
 * @return A node whose previous and next pointers are incorrect or NULL if no
 *         such node exists
 */
static inline header * verify_pointers() {
  for (int i = 0; i < N_LISTS; i++) {
    header * freelist = &freelistSentinels[i];
    for (header * cur = freelist->next; cur != freelist; cur = cur->next) {
      if (cur->next->prev != cur || cur->prev->next != cur) {
        return cur;
      }
    }
  }
  return NULL;
}

/**
 * @brief Verify the structure of the free list is correct by checkin for 
 *        cycles and misdirected pointers
 *
 * @return true if the list is valid
 */
static inline bool verify_freelist() {
  header * cycle = detect_cycles();
  if (cycle != NULL) {
    fprintf(stderr, "Cycle Detected\n");
    print_sublist(print_object, cycle->next, cycle);
    return false;
  }

  header * invalid = verify_pointers();
  if (invalid != NULL) {
    fprintf(stderr, "Invalid pointers\n");
    print_object(invalid);
    return false;
  }

  return true;
}

/**
 * @brief Helper to verify that the sizes in a chunk from the OS are correct
 *        and that allocated node's canary values are correct
 *
 * @param chunk AREA_SIZE chunk allocated from the OS
 *
 * @return a pointer to an invalid header or NULL if all header's are valid
 */
static inline header * verify_chunk(header * chunk) {
	if (get_state(chunk) != FENCEPOST) {
		fprintf(stderr, "Invalid fencepost\n");
		print_object(chunk);
		return chunk;
	}
	
	for (; get_state(chunk) != FENCEPOST; chunk = get_right_header(chunk)) {
		if (get_size(chunk)  != get_right_header(chunk)->left_size) {
			fprintf(stderr, "Invalid sizes\n");
			print_object(chunk);
			return chunk;
		}
	}
	
	return NULL;
}

/**
 * @brief For each chunk allocated by the OS verify that the boundary tags
 *        are consistent
 *
 * @return true if the boundary tags are valid
 */
static inline bool verify_tags() {
  for (size_t i = 0; i < numOsChunks; i++) {
    header * invalid = verify_chunk(osChunkList[i]);
    if (invalid != NULL) {
      return invalid;
    }
  }

  return NULL;
}

/**
 * @brief Initialize mutex lock and prepare an initial chunk of memory for allocation
 */
static void init() {
  // Initialize mutex for thread safety
  pthread_mutex_init(&mutex, NULL);

#ifdef DEBUG
  // Manually set printf buffer so it won't call malloc when debugging the allocator
  setvbuf(stdout, NULL, _IONBF, 0);
#endif // DEBUG

  // Allocate the first chunk from the OS
  header * block = allocate_chunk(ARENA_SIZE);

  header * prevFencePost = get_header_from_offset(block, -ALLOC_HEADER_SIZE);
  insert_os_chunk(prevFencePost);

  lastFencePost = get_header_from_offset(block, get_size(block));

  // Set the base pointer to the beginning of the first fencepost in the first
  // chunk from the OS
  base = ((char *) block) - ALLOC_HEADER_SIZE; //sizeof(header);

  // Initialize freelist sentinels
  for (int i = 0; i < N_LISTS; i++) {
    header * freelist = &freelistSentinels[i];
    freelist->next = freelist;
    freelist->prev = freelist;
  }

  // Insert first chunk into the free list
  header * freelist = &freelistSentinels[N_LISTS - 1];
  freelist->next = block;
  freelist->prev = block;
  block->next = freelist;
  block->prev = freelist;
}

/* 
 * External interface
 */
void * my_malloc(size_t size) {
  pthread_mutex_lock(&mutex);
  header * hdr = allocate_object(size); 
  pthread_mutex_unlock(&mutex);
  return hdr;
}

void * my_calloc(size_t nmemb, size_t size) {
  return memset(my_malloc(size * nmemb), 0, size * nmemb);
}

void * my_realloc(void * ptr, size_t size) {
  void * mem = my_malloc(size);
  memcpy(mem, ptr, size);
  my_free(ptr);
  return mem; 
}

void my_free(void * p) {
  pthread_mutex_lock(&mutex);
  deallocate_object(p);
  pthread_mutex_unlock(&mutex);
}

bool verify() {
  return verify_freelist() && verify_tags();
}

(in-package "ACL2")

(include-book "std/util/define" :dir :system)
(include-book "std/lists/top" :dir :system)

(set-induction-depth-limit 1)

(defun vertex-count (tree)
  (if (atom tree)
    1
    (+ 1
       (vertex-count (car tree))
       (vertex-count (cdr tree)))))

(defun sum-vertex-count (tree-list)
  (if (consp tree-list)
    (+ (vertex-count (car tree-list))
       (sum-vertex-count (cdr tree-list)))
    0))

; H-tree Defintion / Helpers
(defun make-htree (l r)
  (list l r))

; htree-example: added by Mark so he could try executing the various
;   functions defined in this book.
(defun htree-example ()
  (make-htree
    (make-htree
      (make-htree
	"aardvark"
	(make-htree "bat" "crayfish"))
      (make-htree "dingo" "emu"))
    (make-htree
      "frog"
      (make-htree
	(make-htree "gazelle" "hippopotomas")
	"ibix"))))


(defun is-htree (ht)
  (and (true-listp ht)
       (= (length ht) 2)
       (and (or (is-htree (car ht)) (stringp (car ht)))
            (or (is-htree (cadr ht)) (stringp (cadr ht))))))

; path-p: recognizer for paths in an htree
;   A path is a list of 0s and 1s.
;   Optionally, the last element may be a string.
;   Including a search string as the last element lets us distinguish
;   between a return value of nil when there are no occurrences of
;   the search string in the htree, and when the htree is just the
;   string.
(defun path-p (x)
  (or (not x)
      (and (consp x)
	   (or (and (stringp (car x)) (not (cdr x)))
	       (and (or (equal (car x) 0) (equal (car x) 1))
		    (path-p (cdr x)))))))

(defun path-endp (x)
  (or (atom x)
      (and (stringp (car x)) (atom (cdr x)))))

; unstrung-path-p
;   The optional string at the end of a path-p can be a nuisance
;   when reasoning about an in-progress search.  unstrung-path-p
;   recognizes path-p values that don't end with a string.
(defun unstrung-path-p (x)
  (or (not x)
      (and (consp x)
	   (or (equal (car x) 0) (equal (car x) 1))
	   (unstrung-path-p (cdr x)))))

(defthm true-listp-when-unstrung-path-p
  (implies (unstrung-path-p path) (true-listp path)))

(defthm path-p-of-append
  (implies (and (unstrung-path-p path1) (path-p path2))
	   (path-p (append path1 path2))))

; note: writing unstrung-path-p-of-append as showing equality rather than implication
;   was needed to prove unstrung-path-p-of-append.  I might want to strengthen path-p-of-append
;   in the same way.  I don't know if path-p-of-append is used in the proofs in this book.
;   It might be possible to delete path-p-of-append.
(defthm unstrung-path-p-of-append
  (implies
    (true-listp path1)
    (equal (unstrung-path-p (append path1 path2))
      (and (unstrung-path-p path1) (unstrung-path-p path2)))))

(defthm unstrung-path-p-of-rev
  (implies
    (true-listp path)
    (equal (unstrung-path-p (rev path))
	   (unstrung-path-p path))))


(defun unstrung-path-list-p (lst)
  (if (atom lst) (not lst)
    (and (unstrung-path-p (car lst))
	 (unstrung-path-list-p (cdr lst)))))


; (fetch-subtree ht path)
;   Start at ht and return the vertex reached by following path.
(defun fetch-subtree (ht path)
  (cond ((path-endp path) ht)
	((atom ht) nil)
	((equal (car path) 0) (fetch-subtree (car ht) (cdr path)))
	((equal (car path) 1) (fetch-subtree (cadr ht) (cdr path)))
	(t (er hard 'fetch-subtree "bad path: ~x0." path))))

(defthm fetch-subtree-of-append
  (implies
    (unstrung-path-p path1)
    (equal (fetch-subtree ht (append path1 path2))
	   (fetch-subtree (fetch-subtree ht path1) path2))))


; (path-order path1 path2): lexical ordering of paths.
;   Return -1 if path1 < path2; 0 if path1 = path2; or +1 if path1 > path2.
;   We ignore a terminating string if path1 or path2 is a path-p but
;   not an unstrung-path-p.  Thus,
;     (implies (equal path1 path2)
;              (equal (path-order path1 path2) 0))
;   But the converse does not necessarily hold.
(defun path-order (path1 path2)
  (cond ((and (path-endp path1) (path-endp path2)) 0)
	((path-endp path1) -1)
	((path-endp path2)  1)
	((and (integerp (car path1)) (integerp (car path2)))
	 (cond
	   ((< (car path1) (car path2)) -1)
	   ((< (car path2) (car path1))  1)
	   (t (path-order (cdr path1) (cdr path2)))))
	(t nil)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; Traversal Functions


; Head Recursion
(defun head-search (h str) 
  (if (atom h) 
    (and (equal h str) (cons str nil))
    (let ((left (head-search (car h) str)))
      (or (and left (cons 0 left))
	  (let ((right (head-search (cadr h) str)))
	    (and right (cons 1 right)))))))

(defthm path-p-of-head-search
  (implies (stringp str)
	   (path-p (head-search h str))))

(defthm head-search-finds-str
  (let ((path (head-search ht str)))
    (implies (and path (stringp str))
	     (equal (fetch-subtree ht path) str))))


(defthm head-search-finds-least-path
  (implies
    (and (stringp str)
	 (path-p path)
	 (equal (fetch-subtree ht path) str))
    (and (head-search ht str)
         (<= (path-order (head-search ht str) path) 0))))


; Tail Recursion
(defun tail-search* (ht str hts pts path)
  (declare (xargs :measure (+ (vertex-count ht) (sum-vertex-count hts))))
  (if (atom ht)
    (if (equal ht str)
      (rev (cons str path))
      (if (consp hts)
        (tail-search* (car hts) str (cdr hts) (cdr pts) (car pts))
        nil))
    (tail-search* (car ht) str (cons (cadr ht) hts) (cons (cons 1 path) pts)
		  (cons 0 path))))

(defthm path-p-of-tail-search*
  (implies (and (stringp str)
		(unstrung-path-list-p pts)
		(unstrung-path-p path))
           (path-p (tail-search* ht str hts pts path))))

(defun tail-search (ht str)
  (tail-search* ht str nil nil nil))



(defun hts-pts-ok (hts pts root)
  (cond
    ((and (endp hts) (endp pts)) t)
    ((or  (endp hts) (endp pts)) nil)
    (t (and (car hts)
	    (equal (car hts) (fetch-subtree root (rev (car pts))))
	    (hts-pts-ok (cdr hts) (cdr pts) root)))))

(defthm car-of-fetch-subtree
  (implies
    (and (is-htree root)
	 (unstrung-path-p path)
	 (consp (fetch-subtree root path)))
    (car (fetch-subtree root path))))

(defthm cadr-of-fetch-subtree
  (implies
    (and (is-htree root)
	 (unstrung-path-p path)
	 (consp (fetch-subtree root path)))
    (cadr (fetch-subtree root path))))

(defthm path-of-tail-search*
  (let ((path2 (tail-search* ht str hts pts path)))
    (implies (and path2
		  (is-htree root)
		  (equal ht (fetch-subtree root (rev path)))
		  (stringp str)
		  (unstrung-path-list-p pts)
		  (unstrung-path-p path)
	          (hts-pts-ok hts pts root))
	     (equal (fetch-subtree root path2) str)))
  :hints(("Goal" :induct (tail-search* ht str hts pts path))))

(defthm path-of-tail-search
  (let ((path (tail-search root str)))
    (implies (and path (is-htree root) (stringp str))
	     (equal (fetch-subtree root path) str))))


(defun hybrid-search (hts pts str)
  (if (endp hts) nil
    (let ((h (head-search (car hts) str)))
      (if h
	(append (rev (car pts)) h)
	(hybrid-search (cdr hts) (cdr pts) str)))))


(defthmd lemma-findable
  (implies
    (and (is-htree root)
	 (unstrung-path-p path)
	 (equal ht (fetch-subtree root (rev path)))
	 ht
	 (unstrung-path-list-p pts)
	 (hts-pts-ok hts pts root)
	 )
    (equal (tail-search* ht str hts pts path)
	   (hybrid-search (cons ht hts) (cons path pts) str))))

(defthmd lemma-1
  (implies
    (is-htree ht)
    (equal (tail-search ht str)
	   (hybrid-search (list ht) (list nil) str)))
  :hints(("Goal"
    :use((:instance lemma-findable
	    (root ht) (str str) (path nil)
	    (hts nil) (pts nil))))))

(defthmd lemma-2
  (implies
    (is-htree ht)
    (equal (head-search ht str)
	   (hybrid-search (list ht) (list nil) str))))

(defthm tail-search-equals-head-search
  (implies
    (is-htree ht)
    (equal (tail-search ht str)
	   (head-search ht str)))
  :hints(("Goal"
    :use((:instance lemma-1)
	 (:instance lemma-2)))))

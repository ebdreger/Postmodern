(in-package :postmodern)

(defclass dao-class (standard-class)
  ((direct-keys :initarg :keys :initform nil :reader direct-keys)
   (effective-keys :reader dao-keys)
   (table-name)       ; In the interest of views acting like tables, I propose unconditional "table" nomenclature. --EBD
   (column-map :reader dao-column-map))
  (:documentation "Metaclass for database-access-object classes."))

(defmethod dao-keys :before ((class dao-class))
  (unless (class-finalized-p class)
    (finalize-inheritance class)))

(defmethod validate-superclass ((class dao-class) (super-class standard-class))
  t)

(defmethod dao-keys ((class-name symbol))
  (dao-keys (find-class class-name)))

(defmethod dao-keys (dao)
  (mapcar #'(lambda (slot)
              (slot-value dao slot))
          (dao-keys (class-of dao))))

(defun dao-column-slots (class)
  "Enumerate the slots in a class that refer to table rows."
  (mapcar 'slot-column
          (remove-if-not (lambda (x) (typep x 'effective-column-slot))
                         (class-slots class))))
(defun dao-column-fields (class)
  (mapcar 'slot-definition-name (dao-column-slots class)))

(defun dao-table-name (class)
  (when (symbolp class)
    (setf class (find-class class)))
  (if (slot-boundp class 'table-name)
      (slot-value class 'table-name)
      (class-name class)))

(defmethod shared-initialize :before ((class dao-class) slot-names
                                      &key table-name &allow-other-keys)
  (declare (ignore slot-names))
  (setf (slot-value class 'direct-keys) nil)
  (if table-name
      (setf (slot-value class 'table-name)
            (if (symbolp (car table-name)) (car table-name) (intern (car table-name))))
      (slot-makunbound class 'table-name)))

(defun dao-superclasses (class)
  "Build a list of superclasses of a given class that are DAO
  classes."
  (let ((found ()))
    (labels ((explore (class)
               (when (typep class 'dao-class)
                 (pushnew class found))
               (mapc #'explore (class-direct-superclasses class))))
      (explore class)
      found)))

(defmethod finalize-inheritance :after ((class dao-class))
  "Building a row reader and a set of methods can only be done after
  inheritance has been finalised."
  ;; The effective set of keys of a class is the union of its keys and
  ;; the keys of all its superclasses.
  (setf (slot-value class 'effective-keys)
        (reduce 'union (mapcar 'direct-keys (dao-superclasses class))))
  (unless (every (lambda (x) (member x (dao-column-fields class))) (dao-keys class))
    (error "Class ~A has a key that is not also a slot." (class-name class)))
  (build-dao-methods class))

;;; Column-slot code is sufficiently table-centric that it remains in table.lisp, awaiting refactoring. --EBD

(defgeneric dao-exists-p (dao)
  (:documentation "Return a boolean indicating whether the given dao
  exists in the database."))

(defgeneric insert-dao (dao)
  (:documentation "Insert the given object into the database."))

(defgeneric update-dao (dao)
  (:documentation "Update the object's representation in the database
  with the values in the given instance."))

(defgeneric delete-dao (dao)
  (:documentation "Delete the given dao from the database."))

(defgeneric upsert-dao (dao)
  (:documentation "Update or insert the given dao.  If its primary key
  is already in the database and all slots are bound, an update will
  occur.  Otherwise it tries to insert it."))

(defgeneric get-dao (type &rest args)
  (:method ((class-name symbol) &rest args)
    (let ((class (find-class class-name)))
      (if (class-finalized-p class)
          (error "Class ~a has no key slots." (class-name class))
          (finalize-inheritance class))
      (apply 'get-dao class-name args)))
  (:documentation "Get the object corresponding to the given primary
  key, or return nil if it does not exist."))

(defgeneric make-dao (type &rest args &key &allow-other-keys)
  (:method ((class-name symbol) &rest args &key &allow-other-keys)
    (let ((class (find-class class-name)))
      (apply 'make-dao class args)))
  (:method ((class dao-class) &rest args &key &allow-other-keys)
    (unless (class-finalized-p class)
      (finalize-inheritance class))
    (let ((instance (apply #'make-instance class args)))
      (insert-dao instance)))
  (:documentation "Make the instance of the given class and insert it into the database"))

(defmacro define-dao-finalization (((dao-name class) &rest keyword-args) &body body)
  (let ((args-name (gensym)))
    `(defmethod make-dao :around ((class (eql ',class))
				  &rest ,args-name
				  &key ,@keyword-args &allow-other-keys)
       (declare (ignorable ,args-name))
       (let ((,dao-name (call-next-method)))
	 ,@body
	 (update-dao ,dao-name)))))

(defgeneric fetch-defaults (object)
  (:documentation "Used to fetch the default values of an object on
  creation."))

(defun %eval (code)
  (funcall (compile nil `(lambda () ,code))))

;;; #'build-dao-methods : same story as column-slot code. --EBD

(defparameter *custom-column-writers* nil
  "A hook for locally overriding/adding behaviour to DAO row readers.
Should be an alist mapping strings (column names) to symbols or
functions. Symbols are interpreted as slot names that values should be
written to, functions are called with the new object and the value as
arguments.")

(defmacro with-column-writers ((&rest defs) &body body)
  `(let ((*custom-column-writers* (append (list ,@(loop :for (field writer) :on defs :by #'cddr
                                                        :collect `(cons (to-sql-name ,field) ,writer)))
                                          *custom-column-writers*)))
    ,@body))

(defparameter *ignore-unknown-columns* nil)

;;; #'dao-from-fields : same story as column-slot code. --EBD

;;; #'dao-row-reader : depends on #'dao-from-fields

(defun save-dao (dao)
  "Try to insert the content of a DAO. If this leads to a unique key
violation, update it instead."
  (handler-case (progn (insert-dao dao) t)
    (cl-postgres-error:unique-violation ()
      (update-dao dao)
      nil)))

(defun save-dao/transaction (dao)
  (handler-case (with-savepoint save-dao/transaction (insert-dao dao) t)
    (cl-postgres-error:unique-violation ()
      (update-dao dao)
      nil)))

(defun query-dao% (type query row-reader &rest args)
  (let ((class (find-class type)))
    (unless (class-finalized-p class)
      (finalize-inheritance class))
    (if args
	(progn
	  (prepare-query *database* "" query)
	  (exec-prepared *database* "" args row-reader))
	(exec-query *database* query row-reader))))

(defmacro query-dao (type query &rest args)
  "Execute a query and return the result as daos of the given type.
The fields returned by the query must match the slots of the dao, both
by type and by name."
  `(query-dao% ,type ,(real-query query) (dao-row-reader (find-class ,type)) ,@args))

;;; dao-row-reader-with-body : depends on #'dao-from-fields

;;; do-query-dao : depends on dao-row-reader-with-body

(defun generate-dao-query (type &optional (test t) ordering)
  (flet ((check-string (x)
           (if (stringp x) `(:raw ,x) x)))
    (let ((query `(:select '* :from (dao-table-name (find-class ,type))
                   :where ,(check-string test))))
      (when ordering
        (setf query `(:order-by ,query ,@(mapcar #'check-string ordering))))
      query)))

;;; select-dao : depends on dao-row-reader

;;; do-select-dao : depends on dao-row-reader-with-body

(defun dao-table-definition (table)
  "Generate the appropriate CREATE TABLE query for this class."
  (unless (typep table 'dao-class)
    (setf table (find-class table)))
  (unless (class-finalized-p table)
    (finalize-inheritance table))
  (sql-compile
   `(:create-table ,(dao-table-name table)
                   ,(loop :for slot :in (dao-column-slots table)
                          :unless (ghost slot)
                          :collect `(,(slot-definition-name slot) :type ,(column-type slot)
                                     ,@(when (slot-boundp slot 'col-default)
                                             `(:default ,(column-default slot)))))
                   ,@(when (dao-keys table)
                       `((:primary-key ,@(dao-keys table)))))))

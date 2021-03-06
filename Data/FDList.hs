-- | Haskell98
--
-- <http://okmij.org/ftp/Algorithms.html#pure-cyclic-list>
--
-- Pure functional, mutation-free, constant-time-access double-linked
-- lists
--
-- Note that insertions, deletions, lookups have
-- a worst-case complexity of O(min(n,W)), where W is either 32 or 64
-- (depending on the paltform). That means the access time is bounded
-- by a small constant (32 or 64). 
--
--
-- /Pure functional, mutation-free, efficient double-linked lists/
-- 
--     It is always an interesting challenge to write a pure functional and efficient implementation of
--     an imperative algorithm destructively operating a data structure. The functional implementation
--     has a significant benefit of equational reasoning and modularity. We can comprehend the algorithm
--     without keeping the implicit global state in mind. The mutation-free, functional realization has
--     practical benefits: the ease of adding checkpointing, undo and redo. The absence of mutations
--     makes the code multi-threading-safe and helps in porting to distributed or non-shared-memory
--     parallel architectures. On the other hand, an imperative implementation has the advantage of
--     optimality: mutating a component in a complex data structure is a constant-time operation, at
--     least on conventional architectures. Imperative code makes sharing explicit, and so permits
--     efficient implementation of cyclic data structures.
-- 
--     We show a simple example of achieving all the benefits of an imperative data structure --
--     including sharing and the efficiency of updates -- in a pure functional program. Our data
--     structure is a doubly-linked, possibly cyclic list, with the standard operations of adding,
--     deleting and updating elements; traversing the list in both directions; iterating over the list,
--     with cycle detection. The code:
-- 
--       □ uniformly handles both cyclic and terminated lists;
--       □ does not rebuild the whole list on updates;
--       □ updates the value in the current node in time bound by a small constant;
--       □ does not use or mention any monads;
--       □ does not use any IORef, STRef, TVars, or any other destructive updates;
--       □ permits the logging, undoing and redoing of updates, checkpointing;
--       □ easily generalizes to two-dimensional meshes.
-- 
--     The algorithm is essentially imperative, thus permitting identity checking and in-place
--     `updates', but implemented purely functionally. Although the code uses many local, type safe
--     `heaps', there is emphatically no global heap and no global state.
-- 
-- Version: The current version is 1.2, Jan 7, 2009.
--
-- References
--
--    Haskell-Cafe discussion ``Updating doubly linked lists''. January 2009
--
module Data.FDList where

import qualified Data.IntMap as IM

-- | Representation of the double-linked list
type Ref = Int                          -- positive, we shall treat 0 specially

data Node a = Node{node_val   :: a,
                   node_left  :: Ref,
                   node_right :: Ref}

-- | Because DList contains the `pointer' to the current element, DList
-- is also a Zipper
data DList a = DList{dl_counter :: Ref,     -- to generate new Refs
                     dl_current :: Ref,     -- current node
                     dl_mem :: IM.IntMap (Node a)} -- main `memory'


-- | Operations on the DList a
empty :: DList a
empty = DList{dl_counter = 1, dl_current = 0, dl_mem = IM.empty}

-- | In a well-formed list, dl_current must point to a valid node
-- All operations below preserve well-formedness
well_formed :: DList a -> Bool
well_formed dl | IM.null (dl_mem dl) = dl_current dl == 0
well_formed dl = IM.member (dl_current dl) (dl_mem dl)

is_empty :: DList a -> Bool
is_empty dl = IM.null (dl_mem dl)


-- | auxiliary function
get_curr_node :: DList a -> Node a
get_curr_node DList{dl_current=curr,dl_mem=mem} = 
  maybe (error "not well-formed") id $ IM.lookup curr mem

-- | The insert operation below makes a cyclic list
-- The other operations don't care
-- Insert to the right of the current element, if any
-- Return the DL where the inserted node is the current one
insert_right :: a -> DList a -> DList a
insert_right x dl | is_empty dl =
   let ref = dl_counter dl
       -- the following makes the list cyclic
       node = Node{node_val = x, node_left = ref, node_right = ref}
   in DList{dl_counter = succ ref,
            dl_current = ref,
            dl_mem = IM.insert ref node (dl_mem dl)}

insert_right x dl@DList{dl_counter = ref, dl_current = curr, dl_mem = mem} =
  DList{dl_counter = succ ref, dl_current = ref, 
        dl_mem = IM.insert ref  new_node   $ 
                 IM.insert next next_node' $
                 (if next == curr then mem else IM.insert curr curr_node' mem)}
 where
 curr_node = get_curr_node dl
 curr_node'= curr_node{node_right = ref}
 next      = node_right curr_node
 next_node = if next == curr then curr_node'
                else maybe (error "ill-formed DList") id $ IM.lookup next mem
 new_node  = Node{node_val   = x, node_left = curr, node_right = next}
 next_node'= next_node{node_left = ref}
 

-- | Delete the current element from a non-empty list
-- We can handle both cyclic and terminated lists
-- The right node becomes the current node.
-- If the right node does not exists, the left node becomes current
delete :: DList a -> DList a
delete dl@DList{dl_current = curr, dl_mem = mem_old} =
 case () of
   _ | notexist l && notexist r -> empty
   _ | r == 0 ->
       dl{dl_current = l, dl_mem = upd l (\x -> x{node_right=r}) mem}
   _ | r == curr ->                     -- it was a cycle on the right
       dl{dl_current = l, dl_mem = upd l (\x -> x{node_right=l}) mem}
   _ | l == 0 ->
       dl{dl_current = r, dl_mem = upd r (\x -> x{node_left=l}) mem}
   _ | l == curr ->
       dl{dl_current = r, dl_mem = upd r (\x -> x{node_left=r}) mem}
   _ | l == r ->
       dl{dl_current = r, dl_mem = upd r (\x -> x{node_left=r, 
                                                     node_right=r}) mem}
   _ ->
       dl{dl_current = r, dl_mem = upd r (\x -> x{node_left=l}) .
                                   upd l (\x -> x{node_right=r}) $ mem}
 where
 (Just curr_node, mem) = IM.updateLookupWithKey (\_ _ -> Nothing) curr mem_old
 l = node_left curr_node
 r = node_right curr_node
 notexist x = x == 0 || x == curr
 upd ref f mem = IM.adjust f ref mem


get_curr :: DList a -> a
get_curr = node_val . get_curr_node

move_right :: DList a -> Maybe (DList a)
move_right dl = if next == 0 then Nothing else Just (dl{dl_current=next})
 where
 next = node_right $ get_curr_node dl

-- | If no right, just stay inplace
move_right' :: DList a -> DList a
move_right' dl = maybe dl id $ move_right dl

move_left :: DList a -> Maybe (DList a)
move_left dl = if next == 0 then Nothing else Just (dl{dl_current=next})
 where
 next = node_left $ get_curr_node dl

-- | If no left, just stay inplace
move_left' :: DList a -> DList a
move_left' dl = maybe dl id $ move_left dl

fromList :: [a] -> DList a
fromList = foldl (flip insert_right) empty

-- | The following does not anticipate cycles (deliberately)
takeDL :: Int -> DList a -> [a]
takeDL 0 _ = []
takeDL n dl | is_empty dl = []
takeDL n dl = get_curr dl : (maybe [] (takeDL (pred n)) $ move_right dl)

-- | Reverse taking: we move left
takeDLrev :: Int -> DList a -> [a]
takeDLrev 0 _ = []
takeDLrev n dl | is_empty dl = []
takeDLrev n dl = get_curr dl : (maybe [] (takeDLrev (pred n)) $ move_left dl)

-- | Update the current node `inplace'
update :: a -> DList a -> DList a
update x dl@(DList{dl_current = curr, dl_mem = mem}) = 
   dl{dl_mem = IM.insert curr (curr_node{node_val = x}) mem}
  where
  curr_node = get_curr_node dl


-- | This one watches for a cycle and terminates when it detects one
toList :: DList a -> [a]
toList dl | is_empty dl = []
toList dl = get_curr dl : collect (dl_current dl) (move_right dl)
 where
 collect ref0 Nothing = []
 collect ref0 (Just DList{dl_current = curr}) | curr == ref0 = []
 collect ref0 (Just dl) = get_curr dl : collect ref0 (move_right dl)



-- Tests

test1l = insert_right 1 $ empty
test1l_r = takeDL 5 test1l              -- [1,1,1,1,1]
test1l_l = takeDLrev 5 test1l           -- [1,1,1,1,1]
test1l_c = toList test1l                -- [1]

test2l = insert_right 2 $ test1l
test2l_r = takeDL 5 test2l              -- [2,1,2,1,2]
test2l_l = takeDLrev 5 test2l           -- [2,1,2,1,2]
test2l_l'= takeDLrev 5 (move_left' test2l) -- [1,2,1,2,1]
test2l_c = toList test2l                -- [2,1]

test3l = insert_right 3 $ test2l
test3l_r = takeDL 7 test3l              -- [3,1,2,3,1,2,3]
test3l_l = takeDLrev 7 test3l           -- [3,2,1,3,2,1,3]
test3l_l'= takeDLrev 7 (move_left' test3l) -- [2,1,3,2,1,3,2]
test3l_c = toList (move_right' test3l)  -- [1,2,3]


test31l = delete test3l
test31l_r = takeDL 7 test31l            -- [1,2,1,2,1,2,1]
test31l_l = takeDLrev 7 test31l         -- [1,2,1,2,1,2,1]
test31l_c = toList test31l              -- [1,2]

test32l = delete test31l
test32l_r = takeDL 5 test32l            -- [2,2,2,2,2]
test32l_l = takeDLrev 5 test32l         -- [2,2,2,2,2]
test32l_c = toList test32l              -- [2]


test33l = delete test32l
test33l_r = takeDL 5 test33l            -- []


testl = fromList [1..5]
testl_r = takeDL 11 testl               -- [5,1,2,3,4,5,1,2,3,4,5]
testl_l = takeDLrev 11 testl            -- [5,4,3,2,1,5,4,3,2,1,5]
testl_c = toList testl                  -- [5,1,2,3,4]

testl1 = update (-1) testl
testl1_r = takeDL 11 testl1             -- [-1,1,2,3,4,-1,1,2,3,4,-1]
testl1_c = toList testl1                -- [-1,1,2,3,4]

testl2 = update (-2) . move_right' . move_right' $ testl1
testl2_r = takeDL 11 testl2             -- [-2,3,4,-1,1,-2,3,4,-1,1,-2]
testl2_l = takeDLrev 11 testl2          -- [-2,1,-1,4,3,-2,1,-1,4,3,-2]
testl2_c = toList testl2                -- [-2,3,4,-1,1]

-- | Old testl is still available: there are no destructive updates
testl3 = update (-2) . move_right' . move_right' $ testl
testl3_r = takeDL 11 testl3             -- [-2,3,4,5,1,-2,3,4,5,1,-2]
testl3_c = toList testl3                -- [-2,3,4,5,1]


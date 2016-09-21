{-
  Author: @ahmadsalim
  Inspirations by Zork Implementation Language (http://xlisp.org/zil.pdf) and
  Matthew Flatt. 2011. Creating Languages in Racket. Queue 9, 11, Pages 21 (November 2011), 15 pages. DOI: http://dx.doi.org/10.1145/2063166.2068896
-}
{-# OPTIONS_GHC -fwarn-incomplete-patterns #-}
module MiniIF where

import Data.List

newtype Room       = Room String
    deriving (Show, Eq)
newtype Thing      = Thing String
    deriving (Show, Eq)
newtype Verb       = Verb String
    deriving (Show, Eq)
newtype Direction  = Direction String
    deriving (Show, Eq)


data State = State { currentRoom :: Room, mapOfThings :: [(Room, Thing)], inventory :: [Thing], messages :: [String] }
  deriving (Show, Eq)

data GameDesc = GameDesc {
  rooms :: [RoomDesc],
  things :: [ThingDesc],
  verbs :: [VerbDesc]
}
  deriving (Show, Eq)

data RoomDesc = RoomDesc {
  roomName   :: Room,
  roomItems  :: [Thing],
  roomNav    :: [(Direction, Room, Maybe Cond)]
}
  deriving (Show, Eq)

data ThingDesc = ThingDesc {
  thingName :: Thing
}
  deriving (Show, Eq)

data VerbDesc = VerbDesc {
  verbName       :: Verb,
  verbParameters :: [String],
  verbStatements :: [Statement]
}
  deriving (Show, Eq)

data Statement =
    RemoveThing   Term   Term
  | PutThing      Term   Term
  | ChangeRoom    Term
  | IfCond        Cond   [Statement] [Statement]
  | Msg           String
  deriving (Show, Eq)

data Cond =
    HasItem Term Term
  | CanMove Term Term
  | CEq     Term Term
  | CAnd    Cond Cond
  | CNot    Cond
  deriving (Show, Eq)

data Term =
    CurrentRoom
  | Inventory
  | TRoom Room
  | TDirection Direction
  | TThing Thing
  | RoomInDirection Term Term
  | Par String
  deriving (Show, Eq)

data Value = VRoom Room
           | VDirection Direction
           | VThing Thing
           | VInventory
  deriving (Show, Eq)

type Script = [Action]

data Action = Action Verb [Value]
  deriving (Show, Eq)

interpretScript :: GameDesc -> State -> Script -> Maybe State
interpretScript gdesc ps []        = return ps
interpretScript gdesc ps (act:scr) = do
  ps' <- interpretAction gdesc ps act
  interpretScript gdesc ps' scr

interpretAction :: GameDesc -> State -> Action -> Maybe State
interpretAction gdesc ps (Action verb args) = do
  vd <- find ((== verb) . verbName) $ verbs gdesc
  if length (verbParameters vd) == length args
  then interpretStatements gdesc ps (zip (verbParameters vd) args) (verbStatements vd)
  else Nothing

interpretStatements ::  GameDesc -> State -> [(String, Value)] -> [Statement] -> Maybe State
interpretStatements gdesc ps ctxt []           = return ps
interpretStatements gdesc ps ctxt (stmt:stmts) = do
    ps' <- interpretStatement stmt
    interpretStatements gdesc ps' ctxt stmts
  where interpretStatement :: Statement -> Maybe State
        interpretStatement (RemoveThing tm1 tm2) = do
          v1 <- interpretTerm tm1
          v2 <- interpretTerm tm2
          case v2 of
            VThing thing ->
                 case v1 of
                    VInventory -> return ps { inventory = delete thing $ inventory ps }
                    VRoom room -> return ps { mapOfThings = delete (room, thing) $ mapOfThings ps }
                    _ -> Nothing
            _ -> Nothing
        interpretStatement (PutThing tm1 tm2) = do
          v1 <- interpretTerm tm1
          v2 <- interpretTerm tm2
          case v2 of
            VThing thing ->
                 case v1 of
                    VInventory -> return ps { inventory = thing : inventory ps }
                    VRoom room  -> return ps { mapOfThings = (room, thing) : mapOfThings ps }
                    _ -> Nothing
            _ -> Nothing
        interpretStatement (ChangeRoom tm) = do
            v <- interpretTerm tm
            case v of
              VRoom newroom | newroom `elem`
                                 map roomName (rooms gdesc) ->
                   return ps { currentRoom = newroom }
              _ -> Nothing
        interpretStatement (IfCond cond stmts1 stmts2) = do
            b <- interpretCond cond
            interpretStatements gdesc ps ctxt (if b then stmts1 else stmts2)
        interpretStatement (Msg message) = return ps { messages = message : messages ps }
        interpretTerm :: Term -> Maybe Value
        interpretTerm CurrentRoom = return (VRoom $ currentRoom ps)
        interpretTerm Inventory = return VInventory
        interpretTerm (TRoom room) =
          if room `elem` map roomName (rooms gdesc)
          then return (VRoom room)
          else Nothing
        interpretTerm (TDirection dir) = return (VDirection dir)
        interpretTerm (TThing thing) =
          if thing `elem` map thingName (things gdesc)
          then return (VThing thing)
          else Nothing
        interpretTerm (RoomInDirection tm1 tm2) = do
          v1 <- interpretTerm tm1
          v2 <- interpretTerm tm2
          case (v1, v2) of
            (VRoom room, VDirection dir) -> do
              rd <- find ((== room) . roomName) (rooms gdesc)
              (_, neighbour, _) <- find (\(dir', _, _) -> dir' == dir) (roomNav rd)
              return (VRoom neighbour)
            _ -> Nothing
        interpretTerm (Par idx) = lookup idx ctxt
        interpretCond :: Cond -> Maybe Bool
        interpretCond (HasItem tm1 tm2) = do
          v1 <- interpretTerm tm1
          v2 <- interpretTerm tm2
          case (v1, v2) of
            (VRoom room, VThing thing) ->
              let thingsInRoom = map snd $ filter ((== room) . fst) (mapOfThings ps)
              in return (thing `elem` thingsInRoom)
            (VInventory, VThing thing) -> return (thing `elem` inventory ps)
            _ -> Nothing
        interpretCond (CanMove tm1 tm2) = do
          v1 <- interpretTerm tm1
          v2 <- interpretTerm tm2
          case (v1, v2) of
            (VRoom room, VDirection dir) -> do
              rd <- find ((== room) . roomName) (rooms gdesc)
              (_,_,cond) <- find (\(dir', _, _) -> dir' == dir) (roomNav rd)
              maybe (return True) interpretCond cond
            _ -> return False
        interpretCond (CEq tm1 tm2) = do
          v1 <- interpretTerm tm1
          v2 <- interpretTerm tm2
          case (v1, v2) of
            (VRoom room1, VRoom room2) -> return $ room1 == room2
            (VInventory, VInventory) -> return True
            (VThing th1, VThing th2) -> return $ th1 == th2
            (VDirection dir1, VDirection dir2) -> return $ dir1 == dir2
            _ -> return False
        interpretCond (CAnd cond1 cond2) = (&&) <$> interpretCond cond1 <*> interpretCond cond2
        interpretCond (CNot cond) = not <$> interpretCond cond

-- Example
initialState :: GameDesc -> State
initialState gdesc = State { currentRoom = roomName . head $ rooms gdesc,
                             inventory = [],
                             mapOfThings = concatMap (\rd -> map (\th -> (roomName rd, th)) $ roomItems rd) $ rooms gdesc,
                             messages = []
                           }

infinityRoom :: GameDesc
infinityRoom = GameDesc {
    things = [ThingDesc (Thing "Key"), ThingDesc (Thing "Magic Lock"), ThingDesc (Thing "Physical Lock")],
    rooms = [RoomDesc { roomName = Room "Infinity Room",
                        roomItems = [Thing "Magic Lock", Thing "Physical Lock"],
                        roomNav = [(Direction "Ordinary Door", Room "Infinity Room", Nothing),
                                   (Direction "Magic Door", Room "Infinity Room", Just (CNot (HasItem (TRoom $ Room "Infinity Room") (TThing $ Thing "Magic Lock")))),
                                   (Direction "Physical Door", Room "Infinity Room", Just (CNot (HasItem (TRoom $ Room "Infinity Room") (TThing $ Thing "Physical Lock"))))]
                      }],
    verbs = [VerbDesc { verbName = Verb "Go Through",
                        verbParameters = ["door"],
                        verbStatements = [IfCond (CanMove CurrentRoom (Par "door"))
                                          [ChangeRoom (RoomInDirection CurrentRoom (Par "door")),
                                           IfCond (CEq (Par "door") (TDirection $ Direction "Magic Door")) [PutThing CurrentRoom (TThing $ Thing "Key")] [],
                                           IfCond (CEq CurrentRoom (TRoom $ Room "Infinity Room"))
                                             [RemoveThing CurrentRoom (TThing $ Thing "Magic Lock")] []
                                                                              ] [Msg "You tried to open the door, but the door is locked"]]
                      },
              VerbDesc { verbName = Verb "Grab",
                         verbParameters = ["item"],
                         verbStatements = [IfCond (HasItem CurrentRoom (Par "item"))
                                           [RemoveThing CurrentRoom (Par "item"),
                                            PutThing Inventory (Par "item")] [Msg "You grabbed for the item, but there was nothing but your hallucinations"] ] },
              VerbDesc { verbName = Verb "Open",
                         verbParameters = [],
                         verbStatements = [IfCond (CAnd (HasItem Inventory (TThing $ Thing "Key"))
                                                        (HasItem CurrentRoom (TThing $ Thing "Physical Lock")))
                                           [RemoveThing Inventory (TThing $ Thing "Key"),
                                            RemoveThing CurrentRoom (TThing $ Thing "Physical Lock")] [Msg "You looked in your pockets and couldn't find any fitting key"]]
                       }
              ]
  }

goThroughAllDoorsScript :: Script
goThroughAllDoorsScript =
  [Action (Verb "Go Through") [VDirection $ Direction "Ordinary Door"],
   Action (Verb "Grab") [VThing $ Thing "Key"],
   Action (Verb "Go Through") [VDirection $ Direction "Magic Door"],
   Action (Verb "Grab") [VThing $ Thing "Key"],
   Action (Verb "Go Through") [VDirection $ Direction "Physical Door"],
   Action (Verb "Open") [],
   Action (Verb "Go Through") [VDirection $ Direction "Physical Door"]
  ]

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


data State = State { currentRoom :: Room, mapOfThings :: [(Room, Thing)], inventory :: [Thing] }
  deriving (Show, Eq)

data GameDesc = GameDesc {
  rooms :: [RoomDesc],
  things :: [ThingsDesc],
  verbs :: [VerbDesc]
}
  deriving (Show, Eq)

data RoomDesc = RoomDesc {
  roomName   :: Room,
  roomItems  :: [ThingsDesc],
  roomNav    :: [(Direction, Room, Maybe Cond)]
}
  deriving (Show, Eq)

data ThingsDesc = ThingsDesc {
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
    RemoveThing   Term Term
  | PutThing      Term Term
  | ChangeRoom    Term
  | IfCond        Cond [Statement] [Statement]
  deriving (Show, Eq)

data Cond =
    HasItem Term Term
  | CanMove Term Term Term
  | InRoom  Term
  | CEq     Term Term
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

data Script = Script { actions :: [Action] }
  deriving (Show, Eq)

data Action = Action Verb [Value]
  deriving (Show, Eq)

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
        interpretCond cond = _
